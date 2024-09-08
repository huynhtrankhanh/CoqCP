environment({
  dsu: array([int8], 100),
  hasBeenInitialized: array([int8], 1),
  result: array([int8], 1),
})

procedure('ancestor', { vertex: int8, work: int8 }, () => {
  set('work', get('vertex'))
  range(100, (_) => {
    if (sLess(retrieve('dsu', coerceInt64(get('work')))[0], coerceInt8(0))) {
      ;('break')
    }
    set('work', retrieve('dsu', coerceInt64(get('work')))[0])
  })
  store('result', 0, [get('work')])
  set('work', get('vertex'))
  range(100, (_) => {
    if (sLess(retrieve('dsu', coerceInt64(get('work')))[0], coerceInt8(0))) {
      ;('break')
    }
    store('dsu', coerceInt64(get('work')), [retrieve('result', 0)[0]])
    set('work', retrieve('dsu', coerceInt64(get('work')))[0])
  })
})

procedure('unite', { u: int8, v: int8, z: int8 }, () => {
  call('ancestor', { vertex: get('u') })
  set('u', retrieve('result', 0)[0])
  call('ancestor', { vertex: get('v') })
  set('v', retrieve('result', 0)[0])
  if (get('u') != get('v')) {
    if (
      sLess(
        retrieve('dsu', coerceInt64(get('u')))[0],
        retrieve('dsu', coerceInt64(get('v')))[0]
      )
    ) {
      set('z', get('u'))
      set('u', get('v'))
      set('v', get('z'))
    }
    store('dsu', coerceInt64(get('v')), [
      retrieve('dsu', coerceInt64(get('u')))[0] +
        retrieve('dsu', coerceInt64(get('v')))[0],
    ])
    store('dsu', coerceInt64(get('u')), [get('v')])
    donate(
      getSender(),
      coerceInt256(-retrieve('dsu', coerceInt64(get('v')))[0])
    )
  }
})

procedure('main', {}, () => {
  if (retrieve('hasBeenInitialized', 0)[0] == coerceInt8(0)) {
    store('hasBeenInitialized', 0, [coerceInt8(1)])
    range(100, (i) => {
      store('dsu', i, [coerceInt8(-1)])
    })
  }
  call('unite', { u: retrieve(0), v: retrieve(1) })
})
