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
	//
	// The preorder slice is used as a table indexed by vertex number. If
	// the entry is 0, then the vertex has not yet been visited. If the
	// entry is ^0, then the vertex has already been assigned to a
	// component. Otherwise, the entry is a depth-first, preorder sequence
	// number.
	//
	components := [][]uint32{}
	stack := []uint32{}
	preorder := make([]uint32, numVertices+1)
	i := uint32(1)
	var traverse func(uint32) uint32
	traverse = func(v uint32) uint32 {
		lowlink := i
		preorder[v] = i
		i++
		stack = append(stack, v)
		for _, w := range edges[v] {
			var link uint32
			switch preorder[w] {
			case 0:
				link = traverse(w)
			default:
				link = preorder[w]
			case ^uint32(0):
				// v and w belong to different components.
				continue
			}
			if link < lowlink {
				lowlink = link
			}
		}
		if preorder[v] == lowlink {
			j := len(stack)-1
			for stack[j] != v {
				j--
			}
			c := make([]uint32, len(stack)-j)
			copy(c, stack[j:])
			stack = stack[:j]
			for _, u := range c {
				preorder[u] = ^uint32(0)
			}
			components = append(components, c)
		}
		return lowlink
	}
	for v := uint32(1); v <= numVertices; v++ {
		if preorder[v] == 0 {
			traverse(v)
		}
	}
	return components
}
