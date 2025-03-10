environment({
    data: array([int64], 10), // Global array to store 64-bit integers, size 10 fixed for now
})

procedure('main', {
    i: int64, // loop counter for reading calldata and outer bubble sort loop
    j: int64, // inner bubble sort loop
    current_int: int64, // to hold current integer read from calldata
    temp: int64, // for swapping in bubble sort
    array_size: int64, // size of the input array, fixed to 10 for now.
}, () => {
    set('array_size', 10) // Fixed array size for now.

    // Read 64-bit integers from calldata and store in 'data' array
    range(get('array_size'), (i) => {
        set('current_int', 0); // Initialize current_int to 0
        // Reconstruct 64-bit integer from 8 bytes (big-endian)
        range(8, (byte_index) => {
            set(
                'current_int',
                get('current_int') +
                coerceInt64(retrieve(i * 8 + byte_index)) * (1 << ((7 - byte_index) * 8))
            );
        });
        store('data', get('i'), [get('current_int')]);
    });


    // Bubble Sort algorithm (Ascending Order)
    range(get('array_size'), (i) => { // Outer loop
        range(get('array_size') - get('i') - 1, (j) => { // Inner loop
            if (!less(retrieve('data', get('j') + 1)[0], retrieve('data', get('j'))[0])) { // if data[j] > data[j+1] in unsigned comparison (ascending order)
                // Swap data[j] and data[j+1]
                set('temp', retrieve('data', get('j'))[0]);
                store('data', get('j'), [retrieve('data', get('j' )+ 1)[0]]);
                store('data', get('j') + 1, [get('temp')]);
            }
        });
    });

    // Sorted array is now in 'data' array in global memory (ascending order).

})
