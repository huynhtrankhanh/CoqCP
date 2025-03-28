environment({
  dp: array([int64], 1000000),
})

procedure(
  'main',
  {
    commSize: int64,
    temp: int64,
    remainder: int64,
    N: int64,
    pos_limit: int64,
    b0: int64,
    b1: int64,
    b2: int64,
    b3: int64,
    limit: int64,
    limit_plus_1: int64,
    product: int64,
    i_idx: int64,
    i: int64,
    i_minus_1: int64,
    pos_weight: int64,
    w0: int64,
    w1: int64,
    w2: int64,
    w3: int64,
    weight: int64,
    pos_value: int64,
    v0: int64,
    v1: int64,
    v2: int64,
    v3: int64,
    value: int64,
    current_idx: int64,
    prev_idx: int64,
    prev_val: int64,
    remaining_w: int64,
    prev_remaining_idx: int64,
    prev_remaining_val: int64,
    new_val: int64,
    max_idx: int64,
    max_value: int64,
    j: int64,
    w: int64,
    shift_val: int64,
    mod_val: int64,
  },
  () => {
    set('commSize', communicationSize())
    if (less(get('commSize'), coerceInt64(8))) {
      ;('break')
    } else {
      set('temp', get('commSize') - coerceInt64(4))
      set('remainder', get('temp') % coerceInt64(8))
      if (get('remainder') != coerceInt64(0)) {
        ;('break')
      } else {
        set('N', divide(get('temp'), coerceInt64(8)))
        set('pos_limit', multiply(get('N'), coerceInt64(8)))
        set('b0', coerceInt64(retrieve(get('pos_limit'))) & coerceInt64(255))
        set(
          'b1',
          coerceInt64(retrieve(get('pos_limit') + coerceInt64(1))) &
            coerceInt64(255)
        )
        set(
          'b2',
          coerceInt64(retrieve(get('pos_limit') + coerceInt64(2))) &
            coerceInt64(255)
        )
        set(
          'b3',
          coerceInt64(retrieve(get('pos_limit') + coerceInt64(3))) &
            coerceInt64(255)
        )
        set(
          'limit',
          (get('b0') << coerceInt64(24)) |
            (get('b1') << coerceInt64(16)) |
            (get('b2') << coerceInt64(8)) |
            get('b3')
        )
        set('limit_plus_1', get('limit') + coerceInt64(1))
        set('product', multiply(get('N') + coerceInt64(1), get('limit_plus_1')))
        if (less(coerceInt64(1000000), get('product'))) {
          ;('break')
        } else {
          range(get('N'), (i_idx) => {
            set('i', get('i_idx') + coerceInt64(1))
            set('i_minus_1', get('i') - coerceInt64(1))
            set('pos_weight', multiply(get('i_minus_1'), coerceInt64(4)))
            set(
              'w0',
              coerceInt64(retrieve(get('pos_weight'))) & coerceInt64(255)
            )
            set(
              'w1',
              coerceInt64(retrieve(get('pos_weight') + coerceInt64(1))) &
                coerceInt64(255)
            )
            set(
              'w2',
              coerceInt64(retrieve(get('pos_weight') + coerceInt64(2))) &
                coerceInt64(255)
            )
            set(
              'w3',
              coerceInt64(retrieve(get('pos_weight') + coerceInt64(3))) &
                coerceInt64(255)
            )
            set(
              'weight',
              (get('w0') << coerceInt64(24)) |
                (get('w1') << coerceInt64(16)) |
                (get('w2') << coerceInt64(8)) |
                get('w3')
            )
            set(
              'pos_value',
              multiply(coerceInt64(4), get('N')) +
                multiply(get('i_minus_1'), coerceInt64(4))
            )
            set(
              'v0',
              coerceInt64(retrieve(get('pos_value'))) & coerceInt64(255)
            )
            set(
              'v1',
              coerceInt64(retrieve(get('pos_value') + coerceInt64(1))) &
                coerceInt64(255)
            )
            set(
              'v2',
              coerceInt64(retrieve(get('pos_value') + coerceInt64(2))) &
                coerceInt64(255)
            )
            set(
              'v3',
              coerceInt64(retrieve(get('pos_value') + coerceInt64(3))) &
                coerceInt64(255)
            )
            set(
              'value',
              (get('v0') << coerceInt64(24)) |
                (get('v1') << coerceInt64(16)) |
                (get('v2') << coerceInt64(8)) |
                get('v3')
            )
            range(get('limit_plus_1'), (w) => {
              set('w', get('w'))
              set(
                'current_idx',
                multiply(get('i'), get('limit_plus_1')) + get('w')
              )
              set(
                'prev_idx',
                multiply(get('i_minus_1'), get('limit_plus_1')) + get('w')
              )
              set('prev_val', retrieve('dp', get('prev_idx'))[0])
              if (less(get('w'), get('weight'))) {
                store('dp', get('current_idx'), [get('prev_val')])
              } else {
                set('remaining_w', get('w') - get('weight'))
                set(
                  'prev_remaining_idx',
                  multiply(get('i_minus_1'), get('limit_plus_1')) +
                    get('remaining_w')
                )
                set(
                  'prev_remaining_val',
                  retrieve('dp', get('prev_remaining_idx'))[0]
                )
                set('new_val', get('prev_remaining_val') + get('value'))
                if (less(get('prev_val'), get('new_val'))) {
                  store('dp', get('current_idx'), [get('new_val')])
                } else {
                  store('dp', get('current_idx'), [get('prev_val')])
                }
              }
            })
          })
          set('max_idx', multiply(get('N'), get('limit_plus_1')) + get('limit'))
          set('max_value', retrieve('dp', get('max_idx'))[0])
          if (!less(get('commSize'), coerceInt64(8))) {
            range(8, (j) => {
              store(get('j'), coerceInt8(0))
            })
            set('shift_val', coerceInt64(72057594037927936))
            store(0, coerceInt8(divide(get('max_value'), get('shift_val'))))
            set('shift_val', divide(get('shift_val'), coerceInt64(256)))
            store(
              1,
              coerceInt8(
                divide(get('max_value'), get('shift_val')) % coerceInt64(256)
              )
            )
            set('shift_val', divide(get('shift_val'), coerceInt64(256)))
            store(
              2,
              coerceInt8(
                divide(get('max_value'), get('shift_val')) % coerceInt64(256)
              )
            )
            set('shift_val', divide(get('shift_val'), coerceInt64(256)))
            store(
              3,
              coerceInt8(
                divide(get('max_value'), get('shift_val')) % coerceInt64(256)
              )
            )
            set('shift_val', divide(get('shift_val'), coerceInt64(256)))
            store(
              4,
              coerceInt8(
                divide(get('max_value'), get('shift_val')) % coerceInt64(256)
              )
            )
            set('shift_val', divide(get('shift_val'), coerceInt64(256)))
            store(
              5,
              coerceInt8(
                divide(get('max_value'), get('shift_val')) % coerceInt64(256)
              )
            )
            set('shift_val', divide(get('shift_val'), coerceInt64(256)))
            store(
              6,
              coerceInt8(
                divide(get('max_value'), get('shift_val')) % coerceInt64(256)
              )
            )
            store(7, coerceInt8(get('max_value') % coerceInt64(256)))
          }
        }
      }
    }
  }
)
