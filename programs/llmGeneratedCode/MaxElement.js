// Input: n, followed by n values. Output: the maximum, or 0 for an empty input.
environment({
  input: array([int64], 1),
  printBuffer: array([int8], 20),
})

procedure('main', { n: int64, max: int64, current: int64 }, () => {
  call(ReadUnsignedInt64, { resultArray: 'input' }, '', {})
  set('n', retrieve('input', 0)[0])
  range(get('n'), (i) => {
    call(ReadUnsignedInt64, { resultArray: 'input' }, '', {})
    set('current', retrieve('input', 0)[0])
    if (less(get('max'), get('current'))) {
      set('max', get('current'))
    }
  })
  call(PrintInt64, { buffer: 'printBuffer' }, 'unsigned', { num: get('max') })
  writeChar(coerceInt8(10))
})
