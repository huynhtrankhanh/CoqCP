environment({
  dp: array([int64], 1000000),
  message: array([int32], 1),
  n: array([int64], 1),
})

procedure('get weight', { index: int64 }, () => {
  store('message', 0, [
    coerceInt32(retrieve(4 * get('index'))) * coerceInt32(1 << 24) +
      coerceInt32(retrieve(4 * get('index') + 1)) * coerceInt32(1 << 16) +
      coerceInt32(retrieve(4 * get('index') + 2)) * coerceInt32(1 << 8) +
      coerceInt32(retrieve(4 * get('index') + 3)),
  ])
})

procedure('get value', { index: int64 }, () => {
  store('message', 0, [
    coerceInt32(retrieve(4 * retrieve('n', 0)[0] + 4 * get('index'))) *
      coerceInt32(1 << 24) +
      coerceInt32(retrieve(4 * retrieve('n', 0)[0] + 4 * get('index') + 1)) *
        coerceInt32(1 << 16) +
      coerceInt32(retrieve(4 * retrieve('n', 0)[0] + 4 * get('index') + 2)) *
        coerceInt32(1 << 8) +
      coerceInt32(retrieve(4 * retrieve('n', 0)[0] + 4 * get('index') + 3)),
  ])
})

procedure('store result', { x: int64 }, () => {
  store(0, coerceInt8(get('x') >> 56))
  store(1, coerceInt8((get('x') >> 48) & 255))
  store(2, coerceInt8((get('x') >> 40) & 255))
  store(3, coerceInt8((get('x') >> 32) & 255))
  store(4, coerceInt8((get('x') >> 24) & 255))
  store(5, coerceInt8((get('x') >> 16) & 255))
  store(6, coerceInt8((get('x') >> 8) & 255))
  store(7, coerceInt8(get('x') & 255))
})

procedure('get limit', {}, () => {
  store('message', 0, [
    coerceInt32(retrieve(8 * retrieve('n', 0)[0])) * coerceInt32(1 << 24) +
      coerceInt32(retrieve(8 * retrieve('n', 0)[0])) * coerceInt32(1 << 16) +
      coerceInt32(retrieve(8 * retrieve('n', 0)[0])) * coerceInt32(1 << 8) +
      coerceInt32(retrieve(8 * retrieve('n', 0)[0])),
  ])
})

procedure('main', { limit: int64, weight: int64, value: int64 }, () => {
  store('n', 0, [divide(communicationSize() - 4, 8)])
  call('get limit', {})
  set('limit', coerceInt64(retrieve('message', 0)[0]))
  range(retrieve('n', 0)[0] + 1, (i) => {
    if (i == 0) 'continue'
    range(get('limit') + 1, (cap) => {
      call('get weight', { index: i })
      set('weight', coerceInt64(retrieve('message', 0)[0]))
      call('get value', { index: i })
      set('value', coerceInt64(retrieve('message', 0)[0]))
      if (less(cap, get('weight'))) {
        store('dp', i * (get('limit') + 1) + cap, [
          retrieve('dp', (i - 1) * (get('limit') + 1) + cap)[0],
        ])
      } else {
        if (less(retrieve('dp', (i - 1) * (get('limit') + 1) + cap)[0], retrieve('dp', (i - 1) * (get('limit') + 1) + (cap - get('weight')) + get('value'))[0])) {
          store('dp', i * (get('limit') + 1) + cap, [retrieve('dp', (i - 1) * (get('limit') + 1) + (cap - get('weight')) + get('value'))[0]])
        } else {
          store('dp', i * (get('limit') + 1) + cap, [retrieve('dp', (i - 1) * (get('limit') + 1) + cap)[0]])
        }
      }
    })
  })
  call('store result', { x: retrieve('dp', retrieve('n', 0)[0]) * (get('limit') + 1) + get('limit') })
})
