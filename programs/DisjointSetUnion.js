environment({
  dsu: array([int8], 100),
  hasBeenInitialized: array([int8], 1),
  result: array([int8], 1),
})

procedure('ancestor', { vertex: int8 }, () => {
  range(100, (_) => {
    if (sLess(retrieve('dsu', vertex)[0], coerceInt8(0))) {
      ;('break')
    }
    set('vertex', retrieve('dsu', vertex)[0])
  })
  store('result', [get('vertex')])
})

procedure('main', {}, () => {
  if (retrieve('hasBeenInitialized', 0)[0] == coerceInt8(0)) {
    store('hasBeenInitialized', 0, coerceInt8(1))
    range(100, (i) => {
      store('dsu', i, [coerceInt8(-1)])
    })
  }
})
