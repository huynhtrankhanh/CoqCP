module(PrintInt64)
// Create a buffer to hold characters
environment({
  buffer: array([int8], 20),
})

procedure('unsigned', { num: int64, i: int64, tmpChar: int8 }, () => {
  // Handle special case for 0
  if (get('num') == 0) {
    writeChar(coerceInt8(48))
  } else {
    set('i', 0)

    // Extract digits and store in buffer
    range(20, (j) => {
      if (get('num') == 0) {
        ; ('break')
      }
      set('tmpChar', coerceInt8((get('num') % 10) + 48))
      store('buffer', get('i'), [get('tmpChar')])
      set('num', divide(get('num'), 10))
      set('i', get('i') + 1)
    })

    // Print digits in reverse order
    range(get('i'), (j) => {
      writeChar(retrieve('buffer', get('i') - j - 1)[0])
    })
  }
})

procedure('signed', { num: int64 }, () => {
  if (sLess(get('num'), 0)) {
    set('num', -get('num'))
    writeChar(coerceInt8(45)) // Print '-'
  }
  call('unsigned', { num: get('num') })
})
