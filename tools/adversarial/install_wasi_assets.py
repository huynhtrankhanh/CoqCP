"""Install checksum-pinned build assets; no remote install scripts."""
import argparse
import hashlib
import io
from pathlib import Path
import tarfile
import urllib.request


ASSETS = {
    "wasi-sdk": (
        "https://github.com/WebAssembly/wasi-sdk/releases/download/wasi-sdk-34/wasi-sdk-34.0-x86_64-linux.tar.gz",
        "b761e3a0721dbae9c09a0059e5fdb2bf917d1b4a8a7b430fb3b5aafb0984b2c4"),
    "ocaml-runtime": (
        "https://github.com/ocaml/ocaml/archive/refs/tags/5.4.0.tar.gz",
        "4ab55ac30d247e20f35df20a9f7596e5eb5f92fbbd0f8e3e54838bbc3edf931e"),

}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("asset", choices=ASSETS)
    parser.add_argument("destination", type=Path)
    args = parser.parse_args()
    url, expected = ASSETS[args.asset]
    with urllib.request.urlopen(url, timeout=120) as response:
        data = response.read()
    if hashlib.sha256(data).hexdigest() != expected:
        raise RuntimeError("Build asset checksum mismatch")
    with tarfile.open(fileobj=io.BytesIO(data)) as archive:
        args.destination.mkdir(parents=True, exist_ok=True)
        archive.extractall(args.destination, filter="data")


if __name__ == "__main__":
    main()
