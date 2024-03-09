import { PairMap } from './PairMap'

describe('PairMap', () => {
  let pairMap

  beforeEach(() => {
    pairMap = new PairMap()
  })

  test('set and get method', () => {
    pairMap.set([1, 'a'], 'value')
    expect(pairMap.get([1, 'a'])).toBe('value')
  })

  test('get method returns undefined for non-existing pair', () => {
    expect(pairMap.get([2, 'b'])).toBeUndefined()
  })

  test('set method overrides existing value', () => {
    pairMap.set([1, 'a'], 'value1')
    pairMap.set([1, 'a'], 'value2')
    expect(pairMap.get([1, 'a'])).toBe('value2')
  })

  test('set method works for different types of keys', () => {
    pairMap.set([1, 'a'], 'value')
    expect(pairMap.get([1, 'a'])).toBe('value')
    pairMap.set(['x', { key: 'b' }], 'anotherValue')
    expect(pairMap.get(['x', { key: 'b' }])).toBe('anotherValue')
  })

  test('get method returns undefined for non-existing keys', () => {
    pairMap.set([1, 'a'], 'value')
    expect(pairMap.get([2, 'b'])).toBeUndefined()
    expect(pairMap.get([1, 'b'])).toBeUndefined()
    expect(pairMap.get([2, 'a'])).toBeUndefined()
  })

  test('set method works with numeric keys', () => {
    pairMap.set([123, 456], 'value')
    expect(pairMap.get([123, 456])).toBe('value')
  })

  test('set method works with object keys', () => {
    const obj1 = { key: 'obj1' }
    const obj2 = { key: 'obj2' }
    pairMap.set([obj1, obj2], 'value')
    expect(pairMap.get([obj1, obj2])).toBe('value')
  })

  test('set method works with null keys', () => {
    pairMap.set([null, null], 'value')
    expect(pairMap.get([null, null])).toBe('value')
  })

  test('set method works with undefined keys', () => {
    pairMap.set([undefined, undefined], 'value')
    expect(pairMap.get([undefined, undefined])).toBe('value')
  })

  test('set method works with string keys', () => {
    pairMap.set(['key1', 'key2'], 'value')
    expect(pairMap.get(['key1', 'key2'])).toBe('value')
  })
})
