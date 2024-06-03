module(ReadUnsigned64BitInteger)

environment({
  resultArray: array([int64], 1),
})

procedure('', { tmpChar: int64, result: int64 }, () => {
  set('result', 0)

  range(20, (i) => {
    set('tmpChar', readChar())

    if (get('result') == 0 && (less(get('tmpChar'), 48) || !less(get('tmpChar'), 58))) {
      if (coerceInt64(get('tmpChar')) == -1) {
        ;('break')
      }
      ;('continue')
    }

    if (less(get('tmpChar'), 48) || !less(get('tmpChar'), 58)) {
      ;('break')
    }

    set('result', get('result') * 10 + (get('tmpChar') - 48))

    if (get('result') >= 10000000000000000000) {  # Ensure it does not overflow beyond 20 digits
      ;('break')
    }
  })

  store('resultArray', 0, [get('result')])
})
