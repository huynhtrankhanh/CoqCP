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

procedure('unite', { u: int8, v: int8, z: int8 }, () => {
  call('ancestor', { vertex: get('u') })
  set('u', retrieve('result', 0)[0])
  call('ancestor', { vertex: get('v') })
  set('v', retrieve('result', 0)[0])
  if (get('u') != get('v')) {
    if (retrieve('dsu', get('u'))[0] < retrieve('dsu', get('v'))[0]) {
      set('z', get('u'))
      set('u', get('v'))
      set('v', get('z'))
    }
    store('dsu', get('v'), [
      retrieve('dsu', get('u'))[0] + retrieve('dsu', get('v'))[0],
    ])
    store('dsu', get('u'), [get('v')])
    donate(getSender(), -retrieve('dsu', get('v')))
  }
})

procedure('main', {}, () => {
  if (retrieve('hasBeenInitialized', 0)[0] == coerceInt8(0)) {
    store('hasBeenInitialized', 0, coerceInt8(1))
    range(100, (i) => {
      store('dsu', i, [coerceInt8(-1)])
    })
  }
  call('unite', { u: retrieve(0), v: retrieval(1) })
})
