environment({
  // Global heap array (adjust capacity as needed)
  heap: array([int32], 100000),
  // Global heap size tracker (number of elements currently in the heap)
  heapSize: array([int32], 1),
})

// siftUp moves the element at the given index upward to restore the heap property.
procedure(
  'siftUp',
  {
    index: int32, // parameter: starting index
    currentIndex: int32, // local variable for current index
    parentIndex: int32, // local variable for parent's index
    temp: int32, // local temporary variable for swapping
  },
  () => {
    set('currentIndex', get('index'))
    range(30, (i) => {
      if (get('currentIndex') == coerceInt32(0)) {
        ;('break')
      }
      // Compute parent index as (currentIndex - 1) / 2 (using unsigned division)
      set(
        'parentIndex',
        divide(get('currentIndex') - coerceInt32(1), coerceInt32(2))
      )
      // If the current element is less than its parent, swap them.
      if (
        less(
          retrieve('heap', coerceInt64(get('currentIndex')))[0],
          retrieve('heap', coerceInt64(get('parentIndex')))[0]
        )
      ) {
        set('temp', retrieve('heap', coerceInt64(get('currentIndex')))[0])
        store('heap', get('currentIndex'), [
          retrieve('heap', coerceInt64(get('parentIndex')))[0],
        ])
        store('heap', coerceInt64(get('parentIndex')), [get('temp')])
        set('currentIndex', get('parentIndex'))
      } else {
        ;('break')
      }
    })
  }
)

// siftDown moves the element at the given index downward to restore the heap property.
procedure(
  'siftDown',
  {
    index: int32, // parameter: starting index
    currentIndex: int32, // local variable for current index
    leftChild: int32, // local variable for left child index
    rightChild: int32, // local variable for right child index
    smallestIndex: int32, // local variable to track the smallest among current and children
    temp: int32, // local temporary variable for swapping
  },
  () => {
    set('currentIndex', get('index'))
    if (retrieve('heapSize', 0)[0] != coerceInt32(0)) {
      range(30, (i) => {
        // Calculate child indices
        set('leftChild', get('currentIndex') * coerceInt32(2) + coerceInt32(1))
        set('rightChild', get('currentIndex') * coerceInt32(2) + coerceInt32(2))
        // Assume current index is the smallest.
        set('smallestIndex', get('currentIndex'))
        // Check left child.
        if (less(get('leftChild'), retrieve('heapSize', 0)[0])) {
          if (
            less(
              retrieve('heap', coerceInt64(get('leftChild')))[0],
              retrieve('heap', coerceInt64(get('smallestIndex')))[0]
            )
          ) {
            set('smallestIndex', get('leftChild'))
          }
        }
        // Check right child.
        if (less(get('rightChild'), retrieve('heapSize', 0)[0])) {
          if (
            less(
              retrieve('heap', coerceInt64(get('rightChild')))[0],
              retrieve('heap', coerceInt64(get('smallestIndex')))[0]
            )
          ) {
            set('smallestIndex', get('rightChild'))
          }
        }
        // If the smallest is the current element, then the heap property holds.
        if (get('smallestIndex') == get('currentIndex')) {
          ;('break')
        }
        // Otherwise, swap the current element with the smallest child.
        set('temp', retrieve('heap', coerceInt64(get('currentIndex')))[0])
        store('heap', coerceInt64(get('currentIndex')), [
          retrieve('heap', coerceInt64(get('smallestIndex')))[0],
        ])
        store('heap', coerceInt64(get('smallestIndex')), [get('temp')])
        set('currentIndex', get('smallestIndex'))
      })
    }
  }
)

// insert adds a new element into the heap.
procedure(
  'insert',
  {
    value: int32, // parameter: the value to insert
    index: int32, // local variable for index where value is inserted
  },
  () => {
    // Place new value at the end of the heap.
    store('heap', retrieve('heapSize', 0)[0], [get('value')])
    // Increase the heap size.
    store('heapSize', 0, [retrieve('heapSize', 0)[0] + coerceInt32(1)])
    // Compute the index of the newly inserted element.
    set('index', retrieve('heapSize', 0)[0] - coerceInt32(1))
    // Restore the heap property.
    call('siftUp', { index: get('index') })
  }
)

// pop removes the minimum element (at the root) from the heap.
procedure(
  'pop',
  {
    index: int64, // local variable for index computations
    temp: int64, // local temporary variable for swapping
  },
  () => {
    if (retrieve('heapSize', 0)[0] != coerceInt32(0)) {
      // Set index to the last element.
      set('index', retrieve('heapSize', 0)[0] - coerceInt32(1))
      // Swap the root with the last element.
      set('temp', retrieve('heap', 0)[0])
      store('heap', 0, [retrieve('heap', coerceInt64(get('index')))[0]])
      store('heap', coerceInt64(get('index')), [get('temp')])
      // Decrement the heap size.
      store('heapSize', 0, [retrieve('heapSize', 0)[0] - coerceInt32(1)])
      // Restore the heap property from the root.
      call('siftDown', { index: coerceInt32(0) })
    }
  }
)

procedure('main', { current: int32, sum: int64 }, () => {
  range(divide(communicationSize(), 4), (i) => {
    set(
      'current',
      coerceInt32(retrieve(i * 4)) * coerceInt32(16777216) +
        coerceInt32(retrieve(i * 4 + 1)) * coerceInt32(65536) +
        coerceInt32(retrieve(i * 4 + 2)) * coerceInt32(256) +
        coerceInt32(retrieve(i * 4 + 3))
    )
    if (retrieve('heapSize', 0)[0] != 0) {
      if (!less(get('current'), retrieve('heap', 0)[0])) {
        set(
          'sum',
          get('sum') + coerceInt64(get('current') - retrieve('heap', 0)[0])
        )
        call('pop', {})
        call('insert', { value: get('current') })
      }
      call('insert', { value: get('current') })
    }
  })
  store(0, coerceInt8(divide(get('current'), coerceInt32(16777216))))
  store(
    1,
    coerceInt8(divide(get('current'), coerceInt32(65536)) % coerceInt32(256))
  )
  store(
    2,
    coerceInt8(divide(get('current'), coerceInt32(256)) % coerceInt32(256))
  )
  store(3, coerceInt8(get('current') % coerceInt32(256)))
})
