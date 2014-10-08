package scc

// Compute the strongly-connected components of the graph. The result is
// topologically sorted; i.e. there is no edge from a vertex in component i to
// a vertex in component j if i<j.
//
// numVertices must be at least one and less than the maximum value for its
// type. The vertices of the graph are the integers from 1 to numVertices.
//
// If edges[v][i] == w for some i, then there is a directed edge in the graph
// from vertex v to vertex w.
//
// If there are no edges originating from a vertex v, then it is acceptable for
// there to be no entry in the edges map for v.
//
// It is not required that the graph be connected.
//
// The set of components is a partition of the vertex set of the graph.
//
// This algorithm is known as Tarjan's algorithm.
func Compute(numVertices uint32, edges map[uint32][]uint32) [][]uint32 {
	components := [][]uint32{}
	stack := make([]uint32, numVertices+1)
	index := make([]uint32, numVertices+1)
	sp := uint32(1)
	var traverse func(uint32) uint32
	traverse = func(m1 uint32) uint32 {
		lowlink := sp
		index[m1] = sp
		stack[sp] = m1
		sp++
		for _, m2 := range edges[m1] {
			var link uint32
			if index[m2] == 0 {
				link = traverse(m2)
			} else {
				link = index[m2]
			}
			if link < lowlink {
				lowlink = link
			}
		}
		if index[m1] == lowlink {
			c := make([]uint32, sp-index[m1])
			copy(c, stack[index[m1]:sp])
			sp = index[m1]
			components = append(components, c)
		}
		return lowlink
	}
	for m := uint32(1); m <= numVertices; m++ {
		if index[m] == 0 {
			traverse(m)
		}
	}
	return components
}
