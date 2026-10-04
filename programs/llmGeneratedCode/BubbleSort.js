// Input: n, followed by n values. Output: the sorted values, one per line.
environment({
  data: array([int64], 1),
  input: array([int64], 1),
  printBuffer: array([int8], 20),
})

procedure('main', { n: int64, temp: int64 }, () => {
  call(ReadUnsignedInt64, { resultArray: 'input' }, '', {})
  set('n', retrieve('input', 0)[0])
  grow('data', get('n'))
  range(get('n'), (i) => {
    call(ReadUnsignedInt64, { resultArray: 'input' }, '', {})
    store('data', i, [retrieve('input', 0)[0]])
  })
  range(get('n'), (i) => {
    range(get('n') - i - 1, (j) => {
      if (less(retrieve('data', j + 1)[0], retrieve('data', j)[0])) {
        set('temp', retrieve('data', j)[0])
        store('data', j, [retrieve('data', j + 1)[0]])
        store('data', j + 1, [get('temp')])
      }
    })
  })
  range(get('n'), (i) => {
    call(PrintInt64, { buffer: 'printBuffer' }, 'unsigned', { num: retrieve('data', i)[0] })
  writeChar(coerceInt8(10))
  })
})
