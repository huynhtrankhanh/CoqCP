environment({
  dsu: array([int8], 100),
  hasBeenInitialized: array([int8], 0),
})

procedure('main', {}, () => {
  if (retrieve('hasBeenInitialized', 0)[0] == coerceInt8(0)) {
    store('hasBeenInitialized', 0, coerceInt8(1))
    range(100, (i) => {
      store('dsu', i, [coerceInt8(-1)])
    })
  }
})
