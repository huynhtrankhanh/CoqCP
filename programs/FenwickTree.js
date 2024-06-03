environment({
  fenwick: array([int64], 200001),
  resultArray: array([int64], 1),
  queryType: array([int64], 1),
  queryIndex: array([int64], 2),
  queryValue: array([int64], 1),
  printBuffer: array([int8], 20),
})

procedure('increase', { idx: int64, value: int64 }, () => {
  set('idx', get('idx') + 1) // Convert 0-based index to 1-based index for Fenwick Tree

  range(30, (i) => {
    if (less(200000, get('idx'))) {
      ;('break')
    }
    set(
      'fenwick',
      get('idx'),
      retrieve('fenwick', get('idx'))[0] + get('value')
    )
    set('idx', get('idx') + (get('idx') & -get('idx')))
  })
})

procedure('query', { idx: int64, sum: int64 }, () => {
  set('sum', 0)
  set('idx', get('idx') + 1) // Convert 0-based index to 1-based index for Fenwick Tree

  range(30, (i) => {
    if (sLess(get('idx', 0))) {
      ;('break')
    }
    set('sum', get('sum') + retrieve('fenwick', get('idx'))[0])
    set('idx', get('idx') - (get('idx') & -get('idx')))
  })

  store('resultArray', 0, [get('sum')])
})

procedure('rangeQuery', { left: int64, right: int64, result: int64 }, () => {
  call('query', { idx: get('right') })
  set('result', get('resultArray')[0])

  call('query', { idx: get('left') - 1 })
  set('result', get('result') - get('resultArray')[0])

  store('resultArray', 0, [get('result')])
})

procedure(
  'main',
  { t: int64, idx: int64, value: int64, left: int64, right: int64 },
  () => {
    call('ReadUnsignedInt64', { resultArray: 'resultArray' }, '', {})
    range(retrieve('resultArray', 0)[0], (i) => {
      call('ReadSignedInt64', { resultArray: 'resultArray' }, '', {})
      set('t', retrieve('resultArray', 0)[0])
      call('ReadSignedInt64', { resultArray: 'resultArray' }, '', {})
      set('idx', retrieve('resultArray', 0)[0])

      if (get('t') == 0) {
        call('ReadSignedInt64', { resultArray: 'resultArray' }, '', {})
        set('value', retrieve('resultArray', 0)[0])
        call('increase', { idx: get('idx'), value: get('value') })
      } else {
        call('ReadSignedInt64', { resultArray: 'resultArray' }, '', {})
        set('right', retrieve('resultArray', 0)[0])
        call('rangeQuery', { left: get('idx'), right: get('right') })
        call('PrintInt64', { buffer: 'printBuffer' }, 'unsigned', {
          num: retrieve('resultArray', 0)[0],
        })
        writeChar(10) // Print newline
      }
    })
  }
)
