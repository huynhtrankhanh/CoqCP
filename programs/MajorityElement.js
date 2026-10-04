// Input: n, followed by n values with a strict majority. Output: the majority value.
environment({
  input: array([int64], 1),
  printBuffer: array([int8], 20),
})

procedure('main', { n: int64, current: int64, count: int64, value: int64 }, () => {
  call(ReadUnsignedInt64, { resultArray: 'input' }, '', {})
  set('n', retrieve('input', 0)[0])
  range(get('n'), (i) => {
    call(ReadUnsignedInt64, { resultArray: 'input' }, '', {})
    set('value', retrieve('input', 0)[0])
    if (get('count') == 0) {
      set('current', get('value'))
    }
    if (get('value') == get('current')) {
      set('count', get('count') + 1)
    } else {
      set('count', get('count') - 1)
    }
  })
  call(PrintInt64, { buffer: 'printBuffer' }, 'unsigned', { num: get('current') })
  writeChar(coerceInt8(10))
})
