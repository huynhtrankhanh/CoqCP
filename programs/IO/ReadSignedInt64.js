module(ReadSignedInt64)

environment({
  resultArray: array([int64], 1),
})

procedure('', { tmpChar: int64, result: int64, sign: int64 }, () => {
  set('result', 0)
  set('sign', 1)

  range(20, (i) => {
    set('tmpChar', readChar())

    if (get('result') == 0 && get('sign') == 1) {
      if (get('tmpChar') == 43) {
        // '+' sign
        set('sign', 1)
        ;('continue')
      } if (get('tmpChar') == 45) {
        // '-' sign
        set('sign', -1)
        ;('continue')
      } if (less(get('tmpChar'), 48) || !less(get('tmpChar'), 58)) {
        if (coerceInt64(get('tmpChar')) == -1) {
          ;('break')
        }
        ;('continue')
      }
    }

    if (less(get('tmpChar'), 48) || !less(get('tmpChar'), 58)) {
      ;('break')
    }

    set('result', get('result') * 10 + (get('tmpChar') - 48))
  })

  set('result', get('result') * get('sign'))
  store('resultArray', 0, [get('result')])
})
