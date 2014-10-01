package tsort

// A dependency value indicates that the object identified by the b field
// depends on the object identified by the a field.
type dependency struct {
	a, b int
}

// Topologically sort the identifiers contained in d assuming that all identifiers
// i satisfy 0<=i<n. If there are cycles, the output only contains those identifiers
// that do not depend on any identifier that participates in a cycle.
func tsort(n int, d []dependency) []int {
	dependents := make([][]int, n)
	counts := make([]int, n)
	stack := []int{}
	output := []int{}
	for i := 0; i < n; i++ {
		dependents[i] = []int{}
	}
	for _, dep := range d {
		counts[dep.b]++
		dependents[dep.a] = append(dependents[dep.a], dep.b)
	}
	for i := 0; i < n; i++ {
		if counts[i] == 0 {
			stack = append(stack, i)
		}
	}
	k := len(stack)
	for k > 0 {
		k--
		e := stack[k]
		stack = stack[:k]
		output = append(output, e)
		for _, b := range dependents[e] {
			counts[b]--
			if counts[b] == 0 {
				stack = append(stack, b)
				k++
			}
		}
	}
	return output
}

type StringDepGraph struct {
	ids  map[string]int
	deps map[int]map[int]bool
}

func NewStringDepGraph() *StringDepGraph {
	return &StringDepGraph{
		ids:  make(map[string]int),
		deps: make(map[int]map[int]bool),
	}
}

func (g *StringDepGraph) ensureId(s string) int {
	id, ok := g.ids[s]
	if !ok {
		id = len(g.ids)
		g.ids[s] = id
	}
	return id
}

func (g *StringDepGraph) ensureDep(aId, bId int) {
	m, ok := g.deps[aId]
	if !ok {
		m = make(map[int]bool)
		g.deps[aId] = m
	}
	m[bId] = true
}

func (g *StringDepGraph) AddDep(a, b string) {
	aId := g.ensureId(a)
	bId := g.ensureId(b)
	g.ensureDep(aId, bId)
}

// The second return value indicates whether the graph contains any cycles.
func (g *StringDepGraph) Tsort() ([]string, bool) {
	d := []dependency{}
	for aId, m := range g.deps {
		for bId, _ := range m {
			d = append(d, dependency{aId, bId})
		}
	}
	n := len(g.ids)
	sortedIds := tsort(n, d)
	sortedStrs := make([]string, len(sortedIds))
	strs := make([]string, n)
	for s, id := range g.ids {
		strs[id] = s
	}
	for i, id := range sortedIds {
		sortedStrs[i] = strs[id]
	}
	return sortedStrs, (n > len(sortedStrs))
}
