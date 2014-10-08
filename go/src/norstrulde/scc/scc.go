package scc

// Compute the strongly-connected components of the graph. The result is
// topologically sorted; i.e. there is no edge from a vertex in component i to
// a vertex in component j if i<j.
func Compute(numVertices uint32, edges map[uint32][]uint32) [][]uint32 {
	components := [][]uint32{}
	stack := make([]uint32, numVertices+1)
	index := make([]int, numVertices+1)
	lowlink := make([]int, numVertices+1)
	sp := 1
	var traverse func(uint32)
	traverse = func(m1 uint32) {
		index[m1] = sp
		lowlink[m1] = sp
		stack[sp] = m1
		sp++
		for _, m2 := range edges[m1] {
			if index[m2] == 0 {
				traverse(m2)
			}
			if lowlink[m2] < lowlink[m1] {
				lowlink[m1] = lowlink[m2]
			}
		}
		if index[m1] == lowlink[m1] {
			c := make([]uint32, sp-index[m1])
			copy(c, stack[index[m1]:sp])
			sp = index[m1]
			components = append(components, c)
		}
	}
	for m := uint32(1); m <= numVertices; m++ {
		if index[m] == 0 {
			traverse(m)
		}
	}
	return components
}
