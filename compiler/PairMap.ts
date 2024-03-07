type Pair<Left, Right> = [Left, Right]

export class PairMap<KeyLeft, KeyRight, Value> {
  private leftToNumber: WeakMap<KeyLeft, number>
  private rightToNumber: WeakMap<KeyRight, number>
  private map: WeakMap<string, Value>

  constructor() {
    this.leftToNumber = new WeakMap()
    this.rightToNumber = new WeakMap()
    this.map = new WeakMap()
  }

  get(pair: Pair<KeyLeft, KeyRight>): Value | undefined {
    const key = this.getKey(pair)
    return this.map.get(key)
  }

  set(pair: Pair<KeyLeft, KeyRight>, value: Value): void {
    const key = this.getKey(pair)
    this.map.set(key, value)

    const leftCount = this.leftToNumber.get(pair[0]) || 0
    this.leftToNumber.set(pair[0], leftCount + 1)

    const rightCount = this.rightToNumber.get(pair[1]) || 0
    this.rightToNumber.set(pair[1], rightCount + 1)
  }

  private getKey(pair: Pair<KeyLeft, KeyRight>): string {
    return `${pair[0]},${pair[1]}`
  }
}
