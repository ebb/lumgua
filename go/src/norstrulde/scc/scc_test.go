package scc

import (
	"testing"
)

type testCase struct {
	numVertices uint32
	edges map[uint32][]uint32
	components [][]uint32
}

var testCases = []testCase{
	{
		numVertices: 1,
		edges: map[uint32][]uint32{
			1: {},
		},
		components: [][]uint32{{1}},
	},
	{
		numVertices: 2,
		edges: map[uint32][]uint32{
			1: {2},
			2: {1},
		},
		components: [][]uint32{{1, 2}},
	},
	{
		numVertices: 2,
		edges: map[uint32][]uint32{
			1: {},
			2: {},
		},
		components: [][]uint32{{1}, {2}},
	},
	{
		numVertices: 4,
		edges: map[uint32][]uint32{
			1: {2},
			2: {1},
			3: {},
			4: {},
		},
		components: [][]uint32{{1, 2}, {3}, {4}},
	},
	{
		numVertices: 4,
		edges: map[uint32][]uint32{
			1: {2},
			2: {1, 3},
			3: {4},
			4: {4},
		},
		components: [][]uint32{{4}, {3}, {1, 2}},
	},
	{
		numVertices: 4,
		edges: map[uint32][]uint32{
			1: {2},
			2: {1, 3},
			3: {4},
			4: {3},
		},
		components: [][]uint32{{3, 4}, {1, 2}},
	},
	{
		numVertices: 7,
		edges: map[uint32][]uint32{
			1: {2, 3},
			2: {4, 5},
			3: {6, 7},
			4: {1},
			5: {6},
			7: {2},
		},
		components: [][]uint32{{6}, {5}, {1, 2, 3, 4, 7}},
	},
	{
		numVertices: 6,
		edges: map[uint32][]uint32{
			1: {2, 4},
			2: {3},
			3: {2},
			4: {5},
			5: {6},
			6: {5, 2},
		},
		components: [][]uint32{{1}, {4}, {2, 3}, {5, 6}},
	},
}

func isPartition(n uint32, p [][]uint32) bool {
	flags := make([]bool, n)
	for _, c := range p {
		for _, m := range c {
			if m < 1 || n < m {
				return false
			}
			if flags[m-1] {
				return false
			}
			flags[m-1] = true
		}
	}
	return true
}

func areComponentsEqual(c1 []uint32, c2 []uint32) bool {
	n := len(c1)
	if n != len(c2) {
		return false
	}
	for _, m1 := range c1 {
		ok := false
		for _, m2 := range c2 {
			if m1 == m2 {
				ok = true
				break
			}
		}
		if !ok {
			return false
		}
	}
	return true
}

func arePartitionsEqual(p1 [][]uint32, p2 [][]uint32) bool {
	n := len(p1)
	if n != len(p2) {
		return false
	}
	for _, c1 := range p1 {
		ok := false
		for _, c2 := range p2 {
			if areComponentsEqual(c1, c2) {
				ok = true
				break
			}
		}
		if !ok {
			return false
		}
	}
	return true
}

func isTsorted(p [][]uint32, edges map[uint32][]uint32) bool {
	for i, c := range p {
		for _, m1 := range c {
			a := edges[m1]
			for j := i+1; j < len(p); j++ {
				for _, m2 := range p[j] {
					for _, m3 := range a {
						if m3 == m2 {
							return false
						}
					}
				}
			}
		}
	}
	return true
}

func TestScc(t *testing.T) {
	for i, testCase := range testCases {
		components := Compute(testCase.numVertices, testCase.edges)
		if !isPartition(testCase.numVertices, components) {
			t.Errorf("Case %d: Result is not a partition.", i)
		}
		if !arePartitionsEqual(components, testCase.components) {
			t.Errorf("Case %d: Incorrectly partitioned.", i)
		}
		if !isTsorted(components, testCase.edges) {
			t.Errorf("Case %d: Not topologically sorted.", i)
		}
	}
}
