"""Compile the existing OCaml runtime and Rocq VM to WASI.

Only evaluator-owned bytecode reaches this builder. Candidate input is never
parsed or linked on the native host. Each output embeds its exact bytecode and
primitive table, so the existing executable/cache identities cover all code.
"""
import fcntl
import hashlib
import json
from pathlib import Path
import re
import shutil
import struct
import subprocess
import tempfile

ROOT = Path('/opt/rocq/wasi')
SDK = ROOT / 'wasi-sdk-34.0-x86_64-linux/bin'
SJ = ['-mllvm', '-wasm-enable-sjlj', '-mllvm', '-wasm-use-legacy-eh=false']
CFLAGS = ['-O2', '-std=gnu11', '-fwrapv', '-fno-strict-aliasing', *SJ]
EMULATION = ['SIGNAL', 'PROCESS_CLOCKS', 'GETPID', 'MMAN']
LIBS = ['-lsetjmp', *['-lwasi-emulated-' + name.lower().replace('_', '-')
                        for name in EMULATION]]
UNIX = '''access addrofstr chdir close_unix channels_unix cst2constr cstringv
    envir_unix errmsg_unix fsync ftruncate getcwd getpid_unix gettimeofday_unix
    gmtime isatty_unix lseek_unix mkdir open_unix opendir closedir readdir
    rewinddir putenv read_unix realpath_unix rename_unix rmdir stat_unix
    strofaddr time times_unix truncate_unix unlink unixsupport_unix write_unix'''.split()


def run(args, *, cwd=None, env=None):
    subprocess.run(list(map(str, args)), cwd=cwd, env=env, check=True)


def sections(path):
    blob = path.read_bytes()
    if blob[-12:] != b'Caml1999X036':
        raise RuntimeError('Unexpected pinned OCaml bytecode format')
    count, = struct.unpack('>I', blob[-16:-12])
    table = len(blob) - 16 - count * 8
    if not 0 < count < 32 or table < 0:
        raise RuntimeError('Invalid evaluator bytecode section table')
    sizes = [struct.unpack_from('>I', blob, table + i * 8 + 4)[0] for i in range(count)]
    offset = table - sum(sizes)
    if offset < 0:
        raise RuntimeError('Invalid evaluator bytecode section sizes')
    result = {}
    for i, size in enumerate(sizes):
        name = blob[table + i * 8:table + i * 8 + 4].decode('ascii')
        if name in result:
            raise RuntimeError('Duplicate evaluator bytecode section')
        result[name] = blob[offset:offset + size]
        offset += size
    return result


def runtime(gate, env):
    directory = ROOT / 'c-runtime'
    directory.mkdir(parents=True, exist_ok=True)
    with (directory / '.build.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        return _runtime(gate, env)


def _runtime(gate, env):
    source = ROOT / 'c-runtime/ocaml-5.4.0'
    identity = hashlib.sha256((gate.TOOLS / 'portable/ocaml-wasi.patch').read_bytes() +
                             Path(__file__).read_bytes() +
                             (gate.TOOLS / 'install_wasi_assets.py').read_bytes()).hexdigest()
    marker = source.parent / 'build.json'
    if marker.is_file() and json.loads(marker.read_bytes()) == identity:
        return source
    if source.exists():
        shutil.rmtree(source)
    if not SDK.is_dir():
        run(['python3', gate.TOOLS / 'install_wasi_assets.py', 'wasi-sdk', ROOT])
    run(['python3', gate.TOOLS / 'install_wasi_assets.py', 'ocaml-runtime', source.parent])
    # No fuzz: a changed pinned source requires a reviewed port update.
    run(['patch', '--batch', '--forward', '--fuzz=0', '-p1', '-i',
         gate.TOOLS / 'portable/ocaml-wasi.patch'], cwd=source)
    flags = [*CFLAGS, '-Wno-unused-command-line-argument']
    cpp = ['-D_WASI_EMULATED_' + name for name in EMULATION]
    run(['./configure', '--host=x86_64-pc-linux-gnu', '--target=wasm32-unknown-wasi',
         '--disable-native-compiler', '--disable-ocamldoc', '--disable-ocamltest',
         '--without-zstd', 'CC=' + str(SDK / 'clang'), 'CFLAGS=' + ' '.join(flags),
         'CPPFLAGS=' + ' '.join(cpp),
         'LDFLAGS=' + ' '.join([*LIBS, '-Wl,-z,stack-size=2097152']),
         'PTHREAD_CFLAGS=-Wno-unused-command-line-argument', 'PTHREAD_LIBS=-lpthread'],
        cwd=source, env=env)
    run(['make', '-j2', 'runtime/libcamlrun.a'], cwd=source, env=env)
    out = source / 'c-stubs'
    out.mkdir()
    num = gate.TOOLCHAIN / '.opam-switch/sources/num.1.6/src'
    inputs = [source / 'otherlibs/unix' / (name + '.c') for name in UNIX]
    inputs += [source / 'otherlibs/str/strstubs.c', num / 'bng.c', num / 'nat_stubs.c']
    # Retain upstream's pure address allocation helpers, excluding socket APIs.
    original = (source / 'otherlibs/unix/socketaddr.c').read_text()
    helpers = original[original.index('CAMLexport value caml_unix_alloc_inet_addr'):
                       original.index('void caml_unix_get_sockaddr')]
    address = source / 'inet_alloc.c'
    address.write_text('#include <netinet/in.h>\n#include <caml/alloc.h>\n' + helpers)
    inputs.append(address)
    for path in inputs:
        extra = ['-DHAS_SOCKETS', '-DHAS_IPV6'] if path.stem in (
            'addrofstr', 'strofaddr', 'inet_alloc') else []
        run([SDK / 'clang', *flags, *cpp, *extra, '-I', source / 'runtime',
             '-I', source / 'otherlibs/unix', '-I', num, '-c', path,
             '-o', out / (path.stem + '.o')], env=env)
    marker.write_text(json.dumps(identity))
    return source


def c_signatures(source, vm, num):
    paths = [*source.rglob('*.c'), *vm.glob('*.c'), *num.glob('*.c')]
    text = '\n'.join(p.read_text() for p in paths if p.name != 'primitives.c')
    # Boxed float entry points are generated by upstream C macros. Read the
    # actual target declarations rather than guessing their call signatures.
    for path in sorted(vm.glob('rocq_*.c')):
        text += subprocess.check_output([SDK / 'clang', *SJ, '-E', '-DNO_NATIVE_COMPUTE',
            *['-D_WASI_EMULATED_' + name for name in EMULATION],
            '-I', source / 'runtime', str(path)], text=True)
    return re.sub(r'/\*.*?\*/', '', text, flags=re.S)


def primitives(names, defined, signatures):
    text = '''#define CAML_INTERNALS
#include <caml/mlvalues.h>
#include <caml/prims.h>
#include <caml/fail.h>
#include <caml/alloc.h>
'''
    for name in names:
        if not re.fullmatch('[A-Za-z_][A-Za-z_0-9]*', name):
            raise RuntimeError('Invalid evaluator primitive name')
        match = re.search(r'\b' + re.escape(name) + r'\s*\(([^()]*)\)\s*\{', signatures)
        # These three pinned Rocq performance-counter primitives take unit;
        # no other unknown declaration may guess an indirect-call signature.
        params = match.group(1) if match else 'value unit' if name in (
            'CAML_init', 'CAML_drop', 'CAML_peek') else None
        if params is None:
            raise RuntimeError('Unknown pinned primitive signature: ' + name)
        if name in defined:
            text += f'extern value {name}({params});\n'
        elif name in ('caml_thread_initialize', 'caml_thread_cleanup', 'caml_thread_id',
                      'caml_thread_self', 'CAML_init', 'CAML_drop', 'caml_unix_lockf'):
            text += f'value {name}({params}) {{ return Val_unit; }}\n'
        elif name == 'CAML_peek':
            text += f'value {name}({params}) {{ return caml_copy_int64(0); }}\n'
        else:
            # An unlinked primitive cannot acquire authority. Its true C arity
            # is still required by WebAssembly's indirect-call type checks.
            text += f'value {name}({params}) {{ caml_invalid_argument("Unavailable WASI primitive: {name}"); }}\n'
    text += 'const c_primitive caml_builtin_cprim[] = {\n'
    text += ''.join(f'(c_primitive){name},\n' for name in names) + '0};\n'
    text += 'const char *const caml_names_of_builtin_cprim[] = {\n'
    text += ''.join(f'"{name}",\n' for name in names) + '0};\n'
    return text


def array(name, data, words=False):
    values = struct.unpack('<' + 'i' * (len(data) // 4), data) if words else [b if b < 128 else b - 256 for b in data]
    kind = 'int' if words else 'char'
    return f'static {kind} {name}[] = {{\n' + ''.join(
        ','.join(str(v) for v in values[i:i + 16]) + ',\n'
        for i in range(0, len(values), 16)) + '};\n'


def build(gate, portable, env, output):
    source = runtime(gate, env)
    vm = source / 'vm-c'
    vm.mkdir(exist_ok=True)
    pinned = gate.TOOLCHAIN / '.opam-switch/sources/rocq-runtime.9.3.0/kernel/byterun'
    for path in pinned.iterdir():
        if path.suffix in ('.c', '.h'):
            shutil.copyfile(path, vm / path.name)
    generated = portable / '_build/default/kernel/byterun'
    for name in ('rocq_instruct.h', 'rocq_arity.h', 'rocq_jumptbl.h'):
        shutil.copyfile(generated / name, vm / name)
    flags = [*CFLAGS, *['-D_WASI_EMULATED_' + name for name in EMULATION]]
    objects = sorted((source / 'c-stubs').glob('*.o'))
    for name in ('rocq_fix_code', 'rocq_float64', 'rocq_memory', 'rocq_values', 'rocq_interp'):
        obj = vm / (name + '.o')
        run([SDK / 'clang', *flags, '-DNO_NATIVE_COMPUTE', '-I', source / 'runtime',
             '-c', vm / (name + '.c'), '-o', obj], env=env)
        objects.append(obj)
    archive = source / 'runtime/libcamlrun.a'
    symbols = subprocess.check_output([SDK / 'llvm-nm', '--defined-only', '--format=posix',
                                      *objects, archive], text=True)
    defined = set(re.findall(r'^(\w+) [TW] ', symbols, re.M))
    signatures = c_signatures(source, vm, gate.TOOLCHAIN / '.opam-switch/sources/num.1.6/src')
    for ml, binary in [('spec_check', 'spec-check'), ('compile_wasi', 'compile-safe'), ('dep_wasi', 'rocq-dep')]:
        embed(gate, portable / '_build/default/coqcp_wasi_gate' / (ml + '.bc'),
              output / (binary + '.wasm'), env, source, objects, defined, signatures)


def compile_bytecode(gate, bytecode, destination, env):
    """Build a trusted test program with the same C runtime and primitive policy."""
    source = runtime(gate, env)
    objects = sorted((source / 'c-stubs').glob('*.o'))
    archive = source / 'runtime/libcamlrun.a'
    symbols = subprocess.check_output([SDK / 'llvm-nm', '--defined-only', '--format=posix',
                                      *objects, archive], text=True)
    defined = set(re.findall(r'^(\w+) [TW] ', symbols, re.M))
    signatures = c_signatures(source, source / 'vm-c',
        gate.TOOLCHAIN / '.opam-switch/sources/num.1.6/src')
    embed(gate, bytecode, destination, env, source, objects, defined, signatures)


def embed(gate, bytecode, destination, env, source, objects, defined, signatures):
    archive = source / 'runtime/libcamlrun.a'
    flags = [*CFLAGS, *['-D_WASI_EMULATED_' + name for name in EMULATION]]
    with tempfile.TemporaryDirectory(prefix='c-embed-', dir=destination.parent) as temporary:
        work = Path(temporary)
        # Marshal only compiler-owned symbol/CRC metadata, with an explicit
        # compatibility check. No integer truncation or candidate processing.
        helper = work / 'metadata.ml'
        helper.write_text('''let () =
 let read p = let c=open_in_bin p in let s=really_input_string c (in_channel_length c) in close_in c; s in
 let v p = (Marshal.from_string (read p) 0 : Obj.t) in
 let b=Marshal.to_string [|("SYMB",v Sys.argv.(1));("CRCS",v Sys.argv.(2))|] [Marshal.Compat_32] in
 let c=open_out_bin Sys.argv.(3) in output_string c b; close_out c
''')
        run([gate.command('ocamlc'), '-o', work / 'metadata.bc', helper], env=env)
        data = sections(bytecode)
        for name in ('SYMB', 'CRCS'):
            (work / name).write_bytes(data[name])
        run([gate.command('ocamlrun'), work / 'metadata.bc', work / 'SYMB', work / 'CRCS', work / 'metadata'], env=env)
        names = [name.decode('ascii') for name in data['PRIM'].split(b'\0') if name]
        code = primitives(names, defined, signatures)
        code += '#include <caml/startup.h>\n#include <caml/sys.h>\n'
        code += array('caml_code', data['CODE'], words=True)
        code += array('caml_data', data['DATA'])
        code += array('caml_sections', (work / 'metadata').read_bytes())
        code += '''int main(int argc, char **argv) {
 caml_byte_program_mode = COMPLETE_EXE;
 caml_startup_code(caml_code, sizeof(caml_code), caml_data, sizeof(caml_data),
                   caml_sections, sizeof(caml_sections), 0, argv);
 caml_do_exit(0); return 0;
}
'''
        cfile = work / 'program.c'
        cfile.write_text(code)
        run([SDK / 'clang', *flags, '-I', source / 'runtime', '-o', work / 'program.wasm',
             cfile, *objects, archive, *LIBS, '-Wl,-z,stack-size=2097152',
             '-Wl,--max-memory=2147483648'], env=env)
        shutil.move(work / 'program.wasm', destination)
