environment({
  // Global heap array (adjust capacity as needed)
  heap: array([int64], 100000),
  // Global heap size tracker (number of elements currently in the heap)
  heapSize: array([int64], 1),
})

// siftUp moves the element at the given index upward to restore the heap property.
procedure(
  'siftUp',
  {
    index: int64, // parameter: starting index
    currentIndex: int64, // local variable for current index
    parentIndex: int64, // local variable for parent's index
    temp: int64, // local temporary variable for swapping
  },
  () => {
    set('currentIndex', get('index'))
    range(30, (i) => {
      if (get('currentIndex') == 0) {
        ;('break')
      }
      // Compute parent index as (currentIndex - 1) / 2 (using unsigned division)
      set('parentIndex', divide(get('currentIndex') - 1, 2))
      // If the current element is less than its parent, swap them.
      if (
        less(
          retrieve('heap', get('currentIndex'))[0],
          retrieve('heap', get('parentIndex'))[0]
        )
      ) {
        set('temp', retrieve('heap', get('currentIndex'))[0])
        store('heap', get('currentIndex'), [
          retrieve('heap', get('parentIndex'))[0],
        ])
        store('heap', get('parentIndex'), [get('temp')])
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
    index: int64, // parameter: starting index
    currentIndex: int64, // local variable for current index
    leftChild: int64, // local variable for left child index
    rightChild: int64, // local variable for right child index
    smallestIndex: int64, // local variable to track the smallest among current and children
    temp: int64, // local temporary variable for swapping
  },
  () => {
    set('currentIndex', get('index'))
    if (retrieve('heapSize', 0)[0] != 0) {
      range(30, (i) => {
        // Calculate child indices
        set('leftChild', get('currentIndex') * 2 + 1)
        set('rightChild', get('currentIndex') * 2 + 2)
        // Assume current index is the smallest.
        set('smallestIndex', get('currentIndex'))
        // Check left child.
        if (less(get('leftChild'), retrieve('heapSize', 0)[0])) {
          if (
            less(
              retrieve('heap', get('leftChild'))[0],
              retrieve('heap', get('smallestIndex'))[0]
            )
          ) {
            set('smallestIndex', get('leftChild'))
          }
        }
        // Check right child.
        if (less(get('rightChild'), retrieve('heapSize', 0)[0])) {
          if (
            less(
              retrieve('heap', get('rightChild'))[0],
              retrieve('heap', get('smallestIndex'))[0]
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
        set('temp', retrieve('heap', get('currentIndex'))[0])
        store('heap', get('currentIndex'), [
          retrieve('heap', get('smallestIndex'))[0],
        ])
        store('heap', get('smallestIndex'), [get('temp')])
        set('currentIndex', get('smallestIndex'))
      })
    }
  }
)

// insert adds a new element into the heap.
procedure(
  'insert',
  {
    value: int64, // parameter: the value to insert
    index: int64, // local variable for index where value is inserted
  },
  () => {
    // Place new value at the end of the heap.
    store('heap', retrieve('heapSize', 0)[0], [get('value')])
    // Increase the heap size.
    store('heapSize', 0, [retrieve('heapSize', 0)[0] + 1])
    // Compute the index of the newly inserted element.
    set('index', retrieve('heapSize', 0)[0] - 1)
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
    if (retrieve('heapSize', 0)[0] != 0) {
      // Set index to the last element.
      set('index', retrieve('heapSize', 0)[0] - 1)
      // Swap the root with the last element.
      set('temp', retrieve('heap', 0)[0])
      store('heap', 0, [retrieve('heap', get('index'))[0]])
      store('heap', get('index'), [get('temp')])
      // Decrement the heap size.
      store('heapSize', 0, [retrieve('heapSize', 0)[0] - 1])
      // Restore the heap property from the root.
      call('siftDown', { index: 0 })
    }
  }
)

procedure('main', {}, () => {})
