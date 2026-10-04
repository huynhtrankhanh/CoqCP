// Input: n capacity, followed by n pairs of weight and value. Output: maximum value.
environment({
  dp: array([int64], 0),
  weights: array([int32], 0),
  values: array([int32], 0),
  message: array([int32], 1),
  n: array([int64], 1),
  input: array([int64], 1),
  printBuffer: array([int8], 20),
})

procedure('get weight', { index: int64 }, () => {
  store('message', 0, [retrieve('weights', get('index'))[0]])
})

procedure('get value', { index: int64 }, () => {
  store('message', 0, [retrieve('values', get('index'))[0]])
})

// Each cell reads only the previous row, then writes one entry of the next row.
procedure(
  'cell',
  {
    row: int64,
    cap: int64,
    limit: int64,
    weight: int64,
    value: int64,
    best: int64,
    withItem: int64,
  },
  () => {
    set('weight', coerceInt64(retrieve('weights', get('row'))[0]))
    set('value', coerceInt64(retrieve('values', get('row'))[0]))
    set('best', retrieve('dp', get('row') * (get('limit') + 1) + get('cap'))[0])
    if (!less(get('cap'), get('weight'))) {
      set(
        'withItem',
        retrieve(
          'dp',
          get('row') * (get('limit') + 1) + (get('cap') - get('weight'))
        )[0] + get('value')
      )
      if (less(get('best'), get('withItem'))) {
        set('best', get('withItem'))
      }
    }
    store('dp', (get('row') + 1) * (get('limit') + 1) + get('cap'), [
      get('best'),
    ])
  }
)

procedure('solve', { limit: int64 }, () => {
  range(retrieve('n', 0)[0], (row) => {
    range(get('limit') + 1, (cap) => {
      call('cell', { row: row, cap: cap, limit: get('limit') })
    })
  })
})

procedure('main', { count: int64, limit: int64 }, () => {
  call(ReadUnsignedInt64, { resultArray: 'input' }, '', {})
  set('count', retrieve('input', 0)[0])
  store('n', 0, [get('count')])
  call(ReadUnsignedInt64, { resultArray: 'input' }, '', {})
  set('limit', retrieve('input', 0)[0])
  grow('weights', get('count'))
  grow('values', get('count'))
  grow('dp', (get('count') + 1) * (get('limit') + 1))
  range(get('count'), (i) => {
    call(ReadUnsignedInt64, { resultArray: 'input' }, '', {})
    store('weights', i, [coerceInt32(retrieve('input', 0)[0])])
    call(ReadUnsignedInt64, { resultArray: 'input' }, '', {})
    store('values', i, [coerceInt32(retrieve('input', 0)[0])])
  })
  call('solve', { limit: get('limit') })
  call(PrintInt64, { buffer: 'printBuffer' }, 'unsigned', {
    num: retrieve('dp', get('count') * (get('limit') + 1) + get('limit'))[0],
  })
  writeChar(coerceInt8(10))
})
