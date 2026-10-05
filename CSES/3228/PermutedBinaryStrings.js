// Query the ten binary digits of zero-based indices, least significant first.
environment({
  input: array([int64], 1),
  answer: array([int64], 1000),
  printBuffer: array([int8], 20),
})

procedure('queryBit', { index: int64, weight: int64 }, () => {
  writeChar(coerceInt8(48 + (divide(get('index'), get('weight')) % 2)))
})

procedure('recordBit', { index: int64, weight: int64, digit: int64 }, () => {
  store('answer', get('index'), [
    retrieve('answer', get('index'))[0] + (get('digit') - 48) * get('weight'),
  ])
})

procedure('readBit', { digit: int64 }, () => {
  // Skip response separators; each bit is read independently of token length.
  range(20, (attempt) => {
    set('digit', readChar())
    if (get('digit') == 48 || get('digit') == 49) {
      ;('break')
    }
  })
  store('input', 0, [get('digit')])
})

procedure('round', { n: int64, weight: int64 }, () => {
  writeChar(coerceInt8(63))
  writeChar(coerceInt8(32))
  range(get('n'), (i) => {
    call('queryBit', { index: i, weight: get('weight') })
  })
  writeChar(coerceInt8(10))
  ;('flush')
  range(get('n'), (i) => {
    call('readBit', {})
    call('recordBit', {
      index: i,
      weight: get('weight'),
      digit: retrieve('input', 0)[0],
    })
  })
  readChar()
})

procedure('printAnswer', { n: int64 }, () => {
  writeChar(coerceInt8(33))
  range(get('n'), (i) => {
    writeChar(coerceInt8(32))
    call(PrintInt64, { buffer: 'printBuffer' }, 'unsigned', {
      num: retrieve('answer', i)[0] + 1,
    })
  })
  writeChar(coerceInt8(10))
  ;('flush')
})

procedure('main', { n: int64, weight: int64 }, () => {
  call(ReadUnsignedInt64, { resultArray: 'input' }, '', {})
  set('n', retrieve('input', 0)[0])
  set('weight', 1)
  range(10, (round) => {
    call('round', { n: get('n'), weight: get('weight') })
    set('weight', 2 * get('weight'))
  })
  call('printAnswer', { n: get('n') })
})
