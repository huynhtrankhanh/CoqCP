// Binary search the smallest i with F[i+1] < S[k-i].
// Sentinel scores at indices 0 and n+1 are answered locally.
environment({
  input: array([int64], 1),
  reply: array([int64], 1),
  printBuffer: array([int8], 20),
})
procedure('query', { country: int8, index: int64, n: int64 }, () => {
  if (get('index') == 0) {
    store('reply', 0, [1000000001])
  } else {
    if (get('index') == get('n') + 1) {
      store('reply', 0, [0])
    } else {
      writeChar(get('country'))
      writeChar(coerceInt8(32))
      call(PrintInt64, { buffer: 'printBuffer' }, 'unsigned', {
        num: get('index'),
      })
      writeChar(coerceInt8(10))
      ;('flush')
      call(ReadUnsignedInt64, { resultArray: 'input' }, '', {})
      store('reply', 0, [retrieve('input', 0)[0]])
    }
  }
})
procedure(
  'main',
  {
    n: int64,
    k: int64,
    lo: int64,
    hi: int64,
    mid: int64,
    j: int64,
    f: int64,
    s: int64,
    answer: int64,
  },
  () => {
    call(ReadUnsignedInt64, { resultArray: 'input' }, '', {})
    set('n', retrieve('input', 0)[0])
    call(ReadUnsignedInt64, { resultArray: 'input' }, '', {})
    set('k', retrieve('input', 0)[0])
    if (less(get('n'), get('k'))) {
      set('lo', get('k') - get('n'))
    }
    set('hi', get('k'))
    if (less(get('n'), get('hi'))) {
      set('hi', get('n'))
    }
    range(17, (round) => {
      if (get('lo') == get('hi')) {
        ;('break')
      }
      set('mid', divide(get('lo') + get('hi'), 2))
      set('j', get('k') - get('mid'))
      call('query', {
        country: coerceInt8(70),
        index: get('mid') + 1,
        n: get('n'),
      })
      set('f', retrieve('reply', 0)[0])
      call('query', { country: coerceInt8(83), index: get('j'), n: get('n') })
      set('s', retrieve('reply', 0)[0])
      if (less(get('f'), get('s'))) {
        set('hi', get('mid'))
      } else {
        set('lo', get('mid') + 1)
      }
    })
    call('query', { country: coerceInt8(70), index: get('lo'), n: get('n') })
    set('f', retrieve('reply', 0)[0])
    call('query', {
      country: coerceInt8(83),
      index: get('k') - get('lo'),
      n: get('n'),
    })
    set('s', retrieve('reply', 0)[0])
    set('answer', get('f'))
    if (less(get('s'), get('answer'))) {
      set('answer', get('s'))
    }
    range('! ', (c) => {
      writeChar(c)
    })
    call(PrintInt64, { buffer: 'printBuffer' }, 'unsigned', {
      num: get('answer'),
    })
    writeChar(coerceInt8(10))
    ;('flush')
  }
)
