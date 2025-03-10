module(MaxFinder)

procedure('main', { count: int64, max: int64, offset: int64, current: int64 }, () => {
  // Calculate the number of 64-bit integers in calldata.
  // Each integer occupies 8 bytes.
  set('count', divide(communicationSize(), coerceInt64(8)))
  
  // If there is at least one integer, initialize max with the first element.
  if (get('count') != coerceInt64(0)) {
    set('max',
      coerceInt64(retrieve(coerceInt64(0))) * coerceInt64(72057594037927936) +
      coerceInt64(retrieve(coerceInt64(1))) * coerceInt64(281474976710656) +
      coerceInt64(retrieve(coerceInt64(2))) * coerceInt64(1099511627776) +
      coerceInt64(retrieve(coerceInt64(3))) * coerceInt64(4294967296) +
      coerceInt64(retrieve(coerceInt64(4))) * coerceInt64(16777216) +
      coerceInt64(retrieve(coerceInt64(5))) * coerceInt64(65536) +
      coerceInt64(retrieve(coerceInt64(6))) * coerceInt64(256) +
      coerceInt64(retrieve(coerceInt64(7)))
    )
    
    // Loop over remaining elements (from 1 to count-1).
    range(get('count') - coerceInt64(1), (i) => {
      // Compute the byte offset for the current element: (i + 1) * 8.
      set('offset', (i + coerceInt64(1)) * coerceInt64(8))
      
      // Decode the current 64-bit integer from calldata in big endian format.
      set('current',
        coerceInt64(retrieve(get('offset'))) * coerceInt64(72057594037927936) +
        coerceInt64(retrieve(get('offset') + coerceInt64(1))) * coerceInt64(281474976710656) +
        coerceInt64(retrieve(get('offset') + coerceInt64(2))) * coerceInt64(1099511627776) +
        coerceInt64(retrieve(get('offset') + coerceInt64(3))) * coerceInt64(4294967296) +
        coerceInt64(retrieve(get('offset') + coerceInt64(4))) * coerceInt64(16777216) +
        coerceInt64(retrieve(get('offset') + coerceInt64(5))) * coerceInt64(65536) +
        coerceInt64(retrieve(get('offset') + coerceInt64(6))) * coerceInt64(256) +
        coerceInt64(retrieve(get('offset') + coerceInt64(7)))
      )
      
      // If the current element is greater than max, update max.
      if (less(get('max'), get('current'))) {
        set('max', get('current'))
      }
    })
  } else {
    // No elements provided; set max to 0.
    set('max', coerceInt64(0))
  }
  
  // Encode the maximum element into return data in big endian format (8 bytes).
  store(0, coerceInt8(divide(get('max'), coerceInt64(72057594037927936))))
  store(1, coerceInt8(divide(get('max'), coerceInt64(281474976710656)) % coerceInt64(256)))
  store(2, coerceInt8(divide(get('max'), coerceInt64(1099511627776)) % coerceInt64(256)))
  store(3, coerceInt8(divide(get('max'), coerceInt64(4294967296)) % coerceInt64(256)))
  store(4, coerceInt8(divide(get('max'), coerceInt64(16777216)) % coerceInt64(256)))
  store(5, coerceInt8(divide(get('max'), coerceInt64(65536)) % coerceInt64(256)))
  store(6, coerceInt8(divide(get('max'), coerceInt64(256)) % coerceInt64(256)))
  store(7, coerceInt8(get('max') % coerceInt64(256)))
})
