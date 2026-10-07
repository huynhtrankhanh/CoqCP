// Codeforces 1770G. The language has bounded loops and no recursion;
// frames implement the divide-and-conquer traversal explicitly.
environment({
  sequence: array([int8], 0),
  prefix: array([int64], 0),
  factorial: array([int64], 0),
  inverseFactorial: array([int64], 0),
  roots: array([int64], 0),
  work: array([int64], 0),
  other: array([int64], 0),
  poly: array([int64], 0),
  arena: array([int64], 0),
  // interval [l,r), phase, saved polynomial offset and length
  frames: array([int64, int64, int64, int64, int64], 32),
  result: array([int64], 3),
  printBuffer: array([int8], 20),
})

procedure('power', { base: int64, exponent: int64, answer: int64 }, () => {
  set('answer', 1)
  range(64, (i) => {
    if (get('exponent') == 0) { ;('break') }
    if (get('exponent') % 2 == 1) {
      set('answer', get('answer') * get('base') % 998244353)
    }
    set('base', get('base') * get('base') % 998244353)
    set('exponent', divide(get('exponent'), 2))
  })
  store('result', 2, [get('answer')])
})

// Iterative radix-two forward NTT. roots[k+j] = 3^((p-1)j/(2k)).
procedure('ntt', {
  size: int64, j: int64, bit: int64, tmp: int64, k: int64,
  left: int64, right: int64, start: int64,
}, () => {
  range(get('size'), (i) => {
    if (less(i, get('j'))) {
      set('tmp', retrieve('work', i)[0])
      store('work', i, [retrieve('work', get('j'))[0]])
      store('work', get('j'), [get('tmp')])
    }
    set('bit', divide(get('size'), 2))
    range(21, (unused) => {
      if (get('bit') == 0 || less(get('j'), get('bit'))) { ;('break') }
      set('j', get('j') - get('bit'))
      set('bit', divide(get('bit'), 2))
    })
    set('j', get('j') + get('bit'))
  })
  set('k', 1)
  range(20, (stage) => {
    if (!less(get('k'), get('size'))) { ;('break') }
    range(divide(get('size'), 2 * get('k')), (block) => {
      set('start', block * 2 * get('k'))
      range(get('k'), (offset) => {
        set('left', retrieve('work', get('start') + offset)[0])
        set('right', retrieve('roots', get('k') + offset)[0] *
          retrieve('work', get('start') + offset + get('k'))[0] % 998244353)
        store('work', get('start') + offset, [(get('left') + get('right')) % 998244353])
        store('work', get('start') + offset + get('k'),
          [(get('left') + 998244353 - get('right')) % 998244353])
      })
    })
    set('k', get('k') * 2)
  })
})

// Convolve poly[skip..length) with (1+x)^span into arena[base..).
procedure('convolve', {
  skip: int64, length: int64, span: int64, base: int64,
  count: int64, size: int64, scale: int64, tmp: int64,
}, () => {
  set('count', get('length') - get('skip') + get('span'))
  set('size', 1)
  range(20, (i) => {
    if (!less(get('size'), get('count'))) { ;('break') }
    set('size', get('size') * 2)
  })
  range(get('size'), (i) => {
    store('work', i, [0])
    if (less(i, get('length') - get('skip'))) {
      store('work', i, [retrieve('poly', get('skip') + i)[0]])
    }
  })
  call('ntt', { size: get('size') })
  range(get('size'), (i) => {
    store('other', i, [retrieve('work', i)[0]])
    store('work', i, [0])
    if (less(i, get('span') + 1)) {
      store('work', i, [retrieve('factorial', get('span'))[0] *
        retrieve('inverseFactorial', i)[0] % 998244353 *
        retrieve('inverseFactorial', get('span') - i)[0] % 998244353])
    }
  })
  call('ntt', { size: get('size') })
  call('power', { base: get('size'), exponent: 998244351 })
  set('scale', retrieve('result', 2)[0])
  range(get('size'), (i) => {
    store('work', i, [retrieve('work', i)[0] * retrieve('other', i)[0] %
      998244353 * get('scale') % 998244353])
  })
  // Inverse transform = forward transform after index negation and scaling.
  range(divide(get('size') - 1, 2), (index) => {
    set('tmp', retrieve('work', index + 1)[0])
    store('work', index + 1, [retrieve('work', get('size') - index - 1)[0]])
    store('work', get('size') - index - 1, [get('tmp')])
  })
  call('ntt', { size: get('size') })
  range(get('count'), (i) => {
    store('arena', get('base') + i, [retrieve('work', i)[0]])
  })
})

procedure('solve', {
  begin: int64, end: int64, reverse: bool,
  balance: int64, minimum: int64, count: int64,
  depth: int64, top: int64, length: int64,
  l: int64, r: int64, phase: int64, base: int64, saved: int64,
  middle: int64, special: int64, small: int64, hi: int64,
  flag: int64, value: int64, previous: int64, size: int64, ch: int64,
}, () => {
  store('prefix', 0, [0])
  range(get('end') - get('begin'), (i) => {
    if (get('reverse')) {
      set('ch', coerceInt64(retrieve('sequence', get('end') - i - 1)[0]) ^ 1)
    } else {
      set('ch', coerceInt64(retrieve('sequence', get('begin') + i)[0]))
    }
    if (get('ch') == 40) {
      set('balance', get('balance') + 1)
    } else {
      set('balance', get('balance') - 1)
      set('flag', 0)
      if (sLess(get('balance'), get('minimum'))) {
        set('minimum', get('balance'))
        set('flag', 1)
      }
      store('prefix', get('count') + 1, [retrieve('prefix', get('count'))[0] + get('flag')])
      set('count', get('count') + 1)
    }
  })
  store('poly', 0, [1])
  set('length', 1)
  store('frames', 0, [0, get('count'), 0, 0, 0])
  // At most three visits per internal node and one per leaf.
  range(4 * get('count') + 1, (visit) => {
    set('l', retrieve('frames', get('depth'))[0])
    set('r', retrieve('frames', get('depth'))[1])
    set('phase', retrieve('frames', get('depth'))[2])
    set('base', retrieve('frames', get('depth'))[3])
    set('saved', retrieve('frames', get('depth'))[4])
    set('middle', divide(get('l') + get('r'), 2))
    if (get('phase') == 0) {
      if (less(get('r') - get('l'), 33)) {
        range(get('r') - get('l'), (i) => {
          set('flag', retrieve('prefix', get('l') + i + 1)[0] - retrieve('prefix', get('l') + i)[0])
          set('previous', 0)
          if (get('flag') == 0) {
            range(get('length'), (j) => {
              set('value', retrieve('poly', j)[0])
              store('poly', j, [(get('value') + get('previous')) % 998244353])
              set('previous', get('value'))
            })
            store('poly', get('length'), [get('previous')])
            set('length', get('length') + 1)
          } else {
            range(get('length'), (j) => {
              set('value', 0)
              if (less(j + 1, get('length'))) { set('value', retrieve('poly', j + 1)[0]) }
              store('poly', j, [(retrieve('poly', j)[0] + get('value')) % 998244353])
            })
          }
        })
        if (get('depth') == 0) { ;('break') }
        set('depth', get('depth') - 1)
      } else {
        set('special', retrieve('prefix', get('r'))[0] - retrieve('prefix', get('l'))[0])
        set('small', get('special'))
        if (less(get('length'), get('small'))) { set('small', get('length')) }
        set('hi', 0)
        if (less(get('special'), get('length'))) {
          set('hi', get('length') - get('special') + get('r') - get('l'))
          call('convolve', { skip: get('special'), length: get('length'),
            span: get('r') - get('l'), base: get('top') })
        }
        store('frames', get('depth'), [get('l'), get('r'), 1, get('top'), get('hi')])
        set('top', get('top') + get('hi'))
        set('length', get('small'))
        set('depth', get('depth') + 1)
        store('frames', get('depth'), [get('l'), get('middle'), 0, 0, 0])
      }
    } else {
      if (get('phase') == 1) {
        store('frames', get('depth'), [get('l'), get('r'), 2, get('base'), get('saved')])
        set('depth', get('depth') + 1)
        store('frames', get('depth'), [get('middle'), get('r'), 0, 0, 0])
      } else {
        set('size', get('length'))
        if (less(get('size'), get('saved'))) { set('size', get('saved')) }
        range(get('size'), (i) => {
          set('value', 0)
          if (less(i, get('length'))) { set('value', retrieve('poly', i)[0]) }
          if (less(i, get('saved'))) {
            set('value', (get('value') + retrieve('arena', get('base') + i)[0]) % 998244353)
          }
          store('poly', i, [get('value')])
        })
        set('length', get('size'))
        set('top', get('base'))
        if (get('depth') == 0) { ;('break') }
        set('depth', get('depth') - 1)
      }
    }
  })
  store('result', 0, [retrieve('poly', 0)[0]])
})

procedure('main', {
  n: int64, ch: int64, balance: int64, minimum: int64,
  split: int64, size: int64, k: int64, z: int64, answer: int64,
}, () => {
  grow('sequence', 500000)
  range(500001, (i) => {
    set('ch', readChar())
    if (get('ch') != 40 && get('ch') != 41) { ;('break') }
    store('sequence', get('n'), [coerceInt8(get('ch'))])
    set('n', get('n') + 1)
    if (get('ch') == 40) { set('balance', get('balance') + 1) }
    else { set('balance', get('balance') - 1) }
    if (sLess(get('balance'), get('minimum'))) {
      set('minimum', get('balance'))
      set('split', get('n'))
    }
  })
  grow('prefix', get('n') + 1)
  grow('factorial', get('n') + 1)
  grow('inverseFactorial', get('n') + 1)
  grow('poly', 2 * get('n') + 64)
  grow('arena', 4 * get('n') + 128)
  set('size', 1)
  range(20, (i) => {
    if (!less(get('size'), 2 * get('n') + 1)) { ;('break') }
    set('size', get('size') * 2)
  })
  grow('work', get('size'))
  grow('other', get('size'))
  grow('roots', get('size'))
  set('k', 1)
  range(20, (stage) => {
    if (!less(get('k'), get('size'))) { ;('break') }
    call('power', { base: 3, exponent: divide(998244352, 2 * get('k')) })
    set('z', retrieve('result', 2)[0])
    store('roots', get('k'), [1])
    range(get('k') - 1, (i) => {
      store('roots', get('k') + i + 1, [retrieve('roots', get('k') + i)[0] * get('z') % 998244353])
    })
    set('k', get('k') * 2)
  })
  store('factorial', 0, [1])
  range(get('n'), (i) => {
    store('factorial', i + 1, [retrieve('factorial', i)[0] * (i + 1) % 998244353])
  })
  call('power', { base: retrieve('factorial', get('n'))[0], exponent: 998244351 })
  store('inverseFactorial', get('n'), [retrieve('result', 2)[0]])
  range(get('n'), (i) => {
    store('inverseFactorial', get('n') - i - 1,
      [retrieve('inverseFactorial', get('n') - i)[0] * (get('n') - i) % 998244353])
  })
  call('solve', { begin: 0, end: get('split') })
  set('answer', retrieve('result', 0)[0])
  call('solve', { begin: get('split'), end: get('n'), reverse: true })
  set('answer', get('answer') * retrieve('result', 0)[0] % 998244353)
  call(PrintInt64, { buffer: 'printBuffer' }, 'unsigned', { num: get('answer') })
  writeChar(coerceInt8(10))
})
