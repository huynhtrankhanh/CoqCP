environment({
  input: array([int64], 1),
  printBuffer: array([int8], 20),
  dsu: array([int8], 100),
  hasBeenInitialized: array([int8], 1),
  result: array([int8], 1),
})

// Input: q, followed by q pairs of vertices (0..99). Output: component size after each union.
procedure('main', { q: int64, u: int8, v: int8 }, () => {
  call(DSU, { dsu: 'dsu', hasBeenInitialized: 'hasBeenInitialized', result: 'result' }, 'initialize', {})
  call(ReadUnsignedInt64, { resultArray: 'input' }, '', {})
  set('q', retrieve('input', 0)[0])
  range(get('q'), (i) => {
    call(ReadUnsignedInt64, { resultArray: 'input' }, '', {})
    set('u', coerceInt8(retrieve('input', 0)[0]))
    call(ReadUnsignedInt64, { resultArray: 'input' }, '', {})
    set('v', coerceInt8(retrieve('input', 0)[0]))
    call(DSU, { dsu: 'dsu', hasBeenInitialized: 'hasBeenInitialized', result: 'result' }, 'unite', { u: get('u'), v: get('v') })
    call(DSU, { dsu: 'dsu', hasBeenInitialized: 'hasBeenInitialized', result: 'result' }, 'ancestor', { vertex: get('u') })
    call(PrintInt64, { buffer: 'printBuffer' }, 'unsigned', { num: coerceInt64(coerceInt8(-retrieve('dsu', coerceInt64(retrieve('result', 0)[0]))[0])) })
    writeChar(coerceInt8(10))
  })
})
