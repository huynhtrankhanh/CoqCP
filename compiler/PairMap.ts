type Pair<U, V> = [U, V]

function createCounter() {
  let counter = 0
  return () => ++counter
}

export class PairMap<KeyLeft extends object, KeyRight extends object, Value> {
  private leftKeyMap = new WeakMap<object, number>()
  private rightKeyMap = new WeakMap<object, number>()
  private valueMap = new WeakMap<object, Value>()
  private getNextCounter: () => number

  constructor() {
    this.getNextCounter = createCounter()
  }

  private getOrCreateCounterForKey<T>(
    map: WeakMap<object, number>,
    key: T
  ): number {
    if (typeof key === 'object' && key !== null) {
      if (!map.has(key)) {
        map.set(key, this.getNextCounter())
      }
      return map.get(key)!
    } else {
      throw new Error('Key must be a non-null object')
    }
  }

  set(pair: Pair<KeyLeft, KeyRight>, value: Value): void {
    const leftKeyCounter = this.getOrCreateCounterForKey(
      this.leftKeyMap,
      pair[0]
    )
    const rightKeyCounter = this.getOrCreateCounterForKey(
      this.rightKeyMap,
      pair[1]
    )
    const combinedKey = `${leftKeyCounter},${rightKeyCounter}`

    // Use an object as a key to maintain the connection between the counter and the actual value
    const keyObject = { [combinedKey]: true }
    this.valueMap.set(keyObject, value)
  }

  get(pair: Pair<KeyLeft, KeyRight>): Value | undefined {
    const leftKeyCounter = this.leftKeyMap.get(pair[0])
    const rightKeyCounter = this.rightKeyMap.get(pair[1])
    if (leftKeyCounter === undefined || rightKeyCounter === undefined) {
      return undefined // Either part of the pair is not in the map
    }
    const combinedKey = `${leftKeyCounter},${rightKeyCounter}`

    for (const key of this.valueMap.keys()) {
      if (key[combinedKey]) {
        return this.valueMap.get(key)
      }
    }
    return undefined // Pair not found
  }
}
