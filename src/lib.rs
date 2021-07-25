#![allow(non_snake_case)]

use std::fmt;

/// A `SparseGraph` represents an unweighted graph with `V` nodes and `E` edges using the
/// [compressed sparse row](https://en.wikipedia.org/wiki/Sparse_matrix#Compressed_sparse_row_(CSR,_CRS_or_Yale_format)) format.
#[derive(Debug)]
pub struct SparseGraph<'a> {
    idxptr: &'a [usize],  // O(V)
    indices: &'a [usize], // O(E)
}

impl SparseGraph<'_> {
    /// Returns a sparse graph.
    ///
    /// # Arguments
    ///
    /// * `idxptr` - Starting index in `indices` for each vertex. These must be strictly non-decreasing
    /// and less than `indices.len`. The length defines the number of nodes in the graph, `V`
    /// * `indices` - Values in the range `0..V-1` indicating which nodes each vertex is linked to.
    /// The length defines the number edges in the graph, `E`.
    ///
    /// # Panics
    ///
    /// # Example
    ///
    /// ```
    /// use sparse_graph::SparseGraph;
    ///
    /// let (idxptr, indices) = (vec![0, 1, 3, 4, 5, 6], vec![1, 2, 3, 0, 4, 5, 3]);
    /// let g = SparseGraph::new(&idxptr, &indices);
    /// ```
    pub fn new<'a>(idxptr: &'a [usize], indices: &'a [usize]) -> SparseGraph<'a> {
        let edge_count = indices.len();
        if idxptr.is_empty() && idxptr[0] != 0 {
            panic!("Bad index ptr!");
        }
        if edge_count > 0 {
            for index in idxptr.iter() {
                if *index >= edge_count {
                    panic!("Bad index!");
                }
            }
        }
        SparseGraph { idxptr, indices }
    }

    /// Computes the strongly connected components using a memory optimised version of Tarjan's algorithm.
    ///
    /// See <http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.102.1707>.
    ///
    /// Returns
    ///
    /// # Example
    ///
    /// ```
    /// use sparse_graph::{SparseGraph, ConnectedComponents};
    ///
    /// // Create a graph with two strongly connect components
    /// let (idxptr, indices) = (vec![0, 1, 3, 4, 5, 6], vec![1, 2, 3, 0, 4, 5, 3]);
    /// let g = SparseGraph::new(&idxptr, &indices);
    /// let ConnectedComponents { n, labels, sparse_graph } = g.scc();
    /// assert_eq!(n, 2);
    /// assert_eq!(labels, [1, 1, 1, 0, 0, 0]);
    /// assert!(std::ptr::eq(sparse_graph, &g))
    /// ```
    pub fn scc(&self) -> ConnectedComponents {
        let N = self.idxptr.len();
        let END = N + 1;
        let VOID = N + 2;

        let mut lowlinks = vec![VOID; N];
        let mut stack_f = vec![VOID; N];
        let mut stack_b = vec![VOID; N];

        let mut label = N;
        let mut index = 0;
        let mut ss_head = END;

        // Iterate over every node in order
        for v1 in 0..N {
            // If not node hasn't been processed yet, it won't have a lowlink or a label
            if lowlinks[v1] == VOID {
                // DFS-stack push;
                // At this point, the DFS stack is empty, so pushing sets both the
                // forward and backwards pointers to end.
                let mut stack_head = v1;
                stack_f[v1] = END;
                stack_b[v1] = END;
                // We'll now proceed wih the inner loop algorithm until the stack is empty
                while stack_head != END {
                    let v = stack_head;
                    if lowlinks[v] == VOID {
                        // If the top node in the stack hasn't been visited yet,
                        // assign it the next index value.
                        lowlinks[v] = index;
                        index += 1;

                        // Visit all of the nodes accessible from v and push then onto the stack
                        // ahead of v. If they're already in the stack, bring them to the top.
                        let range_end = if v == N - 1 {
                            self.indices.len()
                        } else {
                            self.idxptr[v + 1]
                        };

                        for &w in &self.indices[self.idxptr[v]..range_end] {
                            if lowlinks[w] == VOID {
                                if stack_f[w] != VOID {
                                    // w is already inside the stack, so excise it.
                                    let f = stack_f[w];
                                    let b = stack_b[w];
                                    if b != END {
                                        stack_f[b] = f;
                                    }
                                    if f != END {
                                        stack_b[f] = b;
                                    }
                                }

                                // Add w to the top of the stack. end <-> w <-> stack_head <-> ...
                                stack_f[w] = stack_head;
                                stack_b[w] = END;
                                stack_b[stack_head] = w;
                                stack_head = w;
                            }
                        }
                    } else {
                        // DFS-stack pop
                        stack_head = stack_f[v];
                        // If the stack_head isn't the end
                        if stack_head < N {
                            stack_b[stack_head] = END;
                        }
                        stack_f[v] = VOID;
                        stack_b[v] = VOID;

                        // Find out whether this node is a root node
                        // We look at all its linked nodes (which have now all had this
                        // process applied to them!). If none of them have a lower index than this
                        // node then we have a root value. Otherwise we reset the index to the lowest
                        // index.
                        let mut root = true;
                        let mut low_v = lowlinks[v];
                        let range_end = if v == N - 1 {
                            self.indices.len()
                        } else {
                            self.idxptr[v + 1]
                        };
                        for &w in &self.indices[self.idxptr[v]..range_end] {
                            let low_w = lowlinks[w];
                            if low_w < low_v {
                                low_v = low_w;
                                root = false;
                            }
                        }
                        lowlinks[v] = low_v;
                        let ss = &mut stack_f;
                        if root {
                            // Found a root node. This means we've found the root of
                            // a strongly connected component. All the items on the stack
                            // with an index greater or equal to the current nodes index
                            // are part of the SCC and get the same level.
                            // We can reclaim their index values at this point.

                            // while S not empty and rindex[v] <= rindex[top[S]]
                            while ss_head != END && lowlinks[v] <= lowlinks[ss_head] {
                                let w = ss_head; // w = pop(S)
                                ss_head = ss[w];
                                ss[w] = VOID;
                                let labels = &mut lowlinks;
                                labels[w] = label; // rindex[w] = c;
                                index -= 1; // index = index - 1
                            }
                            let labels = &mut lowlinks;
                            if index > 0 {
                                index -= 1;
                            }
                            labels[v] = label; // rindex[v] = c

                            // Move to the next available label value
                            label -= 1;
                        } else {
                            // We haven't got to the root of this group, so add v to the sets stack
                            ss[v] = ss_head; // push(S, v)
                            ss_head = v;
                        }
                    }
                }
            }
        }
        let labels = &mut lowlinks;

        for label in labels.iter_mut() {
            *label = N - *label
        }
        ConnectedComponents {
            n: N - label,
            labels: lowlinks,
            sparse_graph: self,
        }
    }
}

/// A label map of the connected components of a graph.
pub struct ConnectedComponents<'a> {
    /// The sparse graph associated with the connected components.
    pub sparse_graph: &'a SparseGraph<'a>,
    /// The number of connected components.
    pub n: usize,
    /// A vector of labels from `0` to `n-1`. Corresponding nodes with the same label beloing to the same connected component.
    pub labels: Vec<usize>,
}

impl fmt::Display for SparseGraph<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "SparseGraph: {{").expect("");
        for i in 0..self.indices.len() {
            let start = self.indices[i];
            let end;
            if i == self.indices.len() - 1 {
                end = self.idxptr.len()
            } else {
                end = self.indices[i + 1];
            }
            let node = &self.idxptr[start..end];
            writeln!(f, "  Node {}: {:?}", i, node).expect("");
        }
        write!(f, "}}")
    }
}

#[derive(Debug)]
pub struct WeightedSparseGraph<'a, W> {
    /// Starting index in `indices` for each vertex. These are strictly non-decreasing
    /// and less than `indices.len`. Length is equal to the number of nodes in the graph, `V`.
    idxptr: &'a Vec<usize>,
    /// Values in the range `0..V-1` indicating which nodes each vertex is linked to.
    /// Length is equal to the number edges in the graph, `E`.
    indices: &'a Vec<usize>,

    // Edge weights. The weights correspond to the edges defined in `indices`.
    weights: &'a Vec<W>,
}

#[derive(Debug)]
pub struct ValuedSparseGraph<'a, V> {
    /// Starting index in `indices` for each vertex. These are strictly non-decreasing
    /// and less than `indices.len`. Length is equal to the number of nodes in the graph.
    idxptr: &'a Vec<usize>,
    /// Values `0..N-1` indicating which nodes each vertex is linked to.
    /// Length is equal to the number edges in the graph.
    indices: &'a Vec<usize>,

    // Vertex values. The values correspond to the values in `idxptr`.
    values: Vec<V>,
}

impl<'a, V> ValuedSparseGraph<'a, V> {
    pub fn as_sparse_graph(&self) -> SparseGraph {
        SparseGraph {
            indices: &self.indices,
            idxptr: &self.idxptr,
        }
    }
}

#[derive(Debug)]
pub struct WeightedValuedSparseGraph<'a, W, V> {
    /// Starting index in `indices` for each vertex. These are strictly non-decreasing
    /// and less than `indices.len`. Length is equal to the number of nodes in the graph.
    idxptr: &'a Vec<usize>,
    /// Values `0..N-1` indicating which nodes each vertex is linked to.
    /// Length is equal to the number edges in the graph.
    indices: &'a Vec<usize>,

    // Vertex values. The values correspond to the values in `idxptr`.
    values: &'a Vec<V>,

    // Edge weights. The weights correspond to the edges defined in `indices`.
    weights: &'a Vec<W>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sparse_graph_new() {
        let (a, b) = (vec![0, 1, 2], vec![1, 2, 0]);
        let g = SparseGraph::new(&a, &b);
        assert_eq!(*(g.idxptr), [0, 1, 2]);
        assert_eq!(*g.indices, [1, 2, 0]);
    }

    #[test]
    fn scc_1() {
        let (a, b) = (vec![0, 1, 2], vec![1, 2, 0]);
        let g = SparseGraph::new(&a, &b);
        let ConnectedComponents {
            n,
            labels,
            sparse_graph,
        } = g.scc();
        assert_eq!(n, 1);
        assert_eq!(labels, [0, 0, 0]);
        assert!(std::ptr::eq(sparse_graph, &g))
    }

    #[test]
    fn scc_2() {
        let (a, b) = (vec![0; 3], vec![]);
        let g = SparseGraph::new(&a, &b);
        dbg!(&g);
        let ConnectedComponents { n, labels, .. } = g.scc();
        assert_eq!(n, 3);
        assert_eq!(labels, [0, 1, 2]);
    }

    #[test]
    fn scc_3() {
        let (a, b) = (vec![0, 1, 3, 4, 5, 6], vec![1, 2, 3, 0, 4, 5, 3]);
        let g = SparseGraph::new(&a, &b);
        let ConnectedComponents { n, labels, .. } = g.scc();
        assert_eq!(n, 2);
        assert_eq!(labels, [1, 1, 1, 0, 0, 0]);
    }
}
