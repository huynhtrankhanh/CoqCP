export function topologicalSort(
  nodeCount: number,
  edgeList: [number, number][]
) {
  const graph = edgeListToGraph(edgeList)

  const visited = new Set<number>()
  const result: number[] = []

  function dfs(node: number) {
    visited.add(node)
    const neighbors = graph.get(node) || []
    for (const neighbor of neighbors) {
      if (!visited.has(neighbor)) {
        dfs(neighbor)
      }
    }
    result.push(node)
  }

  for (let node = 0; node < nodeCount; node++) {
    if (!visited.has(node)) {
      dfs(node)
    }
  }

  return result.reverse()
}

function edgeListToGraph(edgeList: [number, number][]): Map<number, number[]> {
  const graph = new Map<number, number[]>()
  for (const [src, dest] of edgeList) {
    if (!graph.has(src)) {
      graph.set(src, [])
    }
    graph.get(src)?.push(dest)
  }
  return graph
}
