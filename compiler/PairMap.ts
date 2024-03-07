type Pair<U, V> = [U, V]

function createCounter() {
  let counter = 0
  return () => ++counter
}

export class PairMap<KeyLeft, KeyRight, Value> {
  private leftKeyMap = new WeakMap<KeyLeft, number>()
  private rightKeyMap = new WeakMap<KeyRight, number>()
  private valueMap = new WeakMap<string, Value>()
  private getNextCounter: () => number

  constructor() {
    this.getNextCounter = createCounter()
  }

  private getOrCreateCounterForKey<T>(
    map: WeakMap<object, number>,
    key: T
  ): number {
      if (!map.has(key)) {
        map.set(key, this.getNextCounter())
      }
      return map.get(key)!
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

    this.valueMap.set(combinedKey, value)
  }

  get(pair: Pair<KeyLeft, KeyRight>): Value | undefined {
    const leftKeyCounter = this.leftKeyMap.get(pair[0])
    const rightKeyCounter = this.rightKeyMap.get(pair[1])
    if (leftKeyCounter === undefined || rightKeyCounter === undefined) {
      return undefined // Either part of the pair is not in the map
    }
    const combinedKey = `${leftKeyCounter},${rightKeyCounter}`

    return this.valueMap.get(combinedKey)
  }
}
