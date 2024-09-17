environment({
  fenwick: array([int64], 200001),
  resultArray: array([int64], 1),
  tempArray: array([int64], 1),
  idxArray: array([int64], 1),
  valueArray: array([int64], 1),
  sumArray: array([int64], 1),
  printBuffer: array([int8], 20),
  n: array([int64], 1),
  q: array([int64], 1),
})

procedure('increase', { idx: int64, value: int64 }, () => {
  store('idxArray', 0, [get('idx') + 1]) // Convert 0-based index to 1-based index for Fenwick Tree
  store('valueArray', 0, [get('value')])
  range(30, (i) => {
    if (less(retrieve('n', 0)[0], retrieve('idxArray', 0)[0])) {
      ;('break')
    }
    store('fenwick', retrieve('idxArray', 0)[0], [
      retrieve('fenwick', retrieve('idxArray', 0)[0])[0] +
        retrieve('valueArray', 0)[0],
    ])
    store('idxArray', 0, [
      retrieve('idxArray', 0)[0] +
        (retrieve('idxArray', 0)[0] & -retrieve('idxArray', 0)[0]),
    ])
  })
})

procedure('query', { idx: int64 }, () => {
  store('sumArray', 0, [0])
  store('idxArray', 0, [get('idx') + 1]) // Convert 0-based index to 1-based index for Fenwick Tree

  range(30, (i) => {
    if (less(retrieve('idxArray', 0)[0], 1)) {
      ;('break')
    }
    store('sumArray', 0, [
      retrieve('sumArray', 0)[0] +
        retrieve('fenwick', retrieve('idxArray', 0)[0])[0],
    ])
    store('idxArray', 0, [
      retrieve('idxArray', 0)[0] -
        (retrieve('idxArray', 0)[0] & -retrieve('idxArray', 0)[0]),
    ])
  })

  store('resultArray', 0, [retrieve('sumArray', 0)[0]])
})

procedure('rangeQuery', { left: int64, right: int64 }, () => {
  call('query', { idx: get('right') })
  store('tempArray', 0, [retrieve('resultArray', 0)[0]])

  call('query', { idx: get('left') - 1 })
  store('tempArray', 0, [
    retrieve('tempArray', 0)[0] - retrieve('resultArray', 0)[0],
  ])

  store('resultArray', 0, [retrieve('tempArray', 0)[0]])
})

procedure('update', { idx: int64, value: int64 }, () => {
  // Get current value at idx
  call('rangeQuery', { left: get('idx'), right: get('idx') })
  store('tempArray', 0, [retrieve('resultArray', 0)[0]])

  // Calculate the delta
  store('tempArray', 0, [get('value') - retrieve('tempArray', 0)[0]])

  // Apply the delta
  call('increase', { idx: get('idx'), value: retrieve('tempArray', 0)[0] })
})

procedure('main', {}, () => {
  call(ReadUnsignedInt64, { resultArray: 'resultArray' }, '', {})
  store('n', 0, [retrieve('resultArray', 0)[0]])
  call(ReadUnsignedInt64, { resultArray: 'resultArray' }, '', {})
  store('q', 0, [retrieve('resultArray', 0)[0]])

  range(retrieve('n', 0)[0], (i) => {
    call(ReadUnsignedInt64, { resultArray: 'resultArray' }, '', {})
    call('increase', { idx: i, value: retrieve('resultArray', 0)[0] })
  })

  range(retrieve('q', 0)[0], (i) => {
    call(ReadUnsignedInt64, { resultArray: 'resultArray' }, '', {})
    store('tempArray', 0, [retrieve('resultArray', 0)[0]])
    call(ReadUnsignedInt64, { resultArray: 'resultArray' }, '', {})
    store('idxArray', 0, [retrieve('resultArray', 0)[0]])

    if (retrieve('tempArray', 0)[0] == 1) {
      call(ReadUnsignedInt64, { resultArray: 'resultArray' }, '', {})
      store('valueArray', 0, [retrieve('resultArray', 0)[0]])
      call('update', {
        idx: retrieve('idxArray', 0)[0] - 1,
        value: retrieve('valueArray', 0)[0],
      })
    } else {
      call(ReadUnsignedInt64, { resultArray: 'resultArray' }, '', {})
      store('tempArray', 0, [retrieve('resultArray', 0)[0]])
      call('rangeQuery', {
        left: retrieve('idxArray', 0)[0] - 1,
        right: retrieve('tempArray', 0)[0] - 1,
      })
      call(PrintInt64, { buffer: 'printBuffer' }, 'unsigned', {
        num: retrieve('resultArray', 0)[0],
      })
      writeChar(coerceInt8(10)) // Print newline
    }
  })
})
