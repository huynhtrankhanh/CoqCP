export function findCycle(edges: [number, number][]): number[] | undefined {
  const n: number = edges.reduce(
    (max, [a, b]) => Math.max(max, a + 1, b + 1),
    0
  )
  const m: number = edges.length
  const maxn: number = n + 1 // Adjusting bounds
  const maxm: number = m + 1

  let head: number[] = Array(maxn).fill(0)
  let values: number[] = Array(maxm).fill(0)
  let visited: boolean[] = Array(maxn).fill(false)
  let positionInPath: number[] = Array(maxn).fill(-1)
  let path: number[] = []

  edges.forEach(([from, to], i) => {
    head[from]++
  })

  for (let i = 1; i <= n; i++) {
    head[i] += head[i - 1]
  }

  edges.forEach(([from, to], i) => {
    values[head[from] - 1] = to
    head[from]--
  })

  const dfs = (vertex: number) => {
    let oldPosition = positionInPath[vertex]
    positionInPath[vertex] = path.length
    path.push(vertex)

    for (let i = head[vertex]; i < head[vertex + 1]; i++) {
      let adjacent = values[i]
      if (positionInPath[adjacent] === -1) {
        if (visited[vertex]) continue
        dfs(adjacent)
      } else {
        // Found a cycle
        let start = positionInPath[adjacent]
        return path.slice(start).concat(adjacent)
      }
    }

    path.pop()
    positionInPath[vertex] = oldPosition
    visited[vertex] = true
  }

  for (let i = 0; i < n; i++) {
    if (visited[i]) continue
    const result = dfs(i)
    if (result) return result
  }

  return undefined // No cycle found
}
