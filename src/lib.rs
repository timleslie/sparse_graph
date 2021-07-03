use std::fmt;

#[derive(Debug)]
pub struct SparseGraph<const N: usize> {
    /// Starting index in indices for each vertex. These are strictly non-decreasing
    /// and less than `indices.len`.
    pub idxptr: [usize; N],
    /// Values `0..N` indicating which nodes each vertex is linked to.
    /// Length is equal to the number edges in the graph.
    pub indices: Vec<usize>,
}

impl<const N: usize> fmt::Display for SparseGraph<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "CSGraph: {{\n").expect("");
        for i in 0..self.indices.len() {
            let start = self.indices[i];
            let end;
            if i == self.indices.len() - 1 {
                end = self.idxptr.len()
            } else {
                end = self.indices[i + 1];
            }
            let foo = &self.idxptr[start..end];
            write!(f, "  Node {}: {:?}\n", i, foo).expect("");
        }
        return write!(f, "}}");
    }
}

impl<const N: usize> SparseGraph<N> {
    pub fn new(idxptr: [usize; N], indices: Vec<usize>) -> SparseGraph<N> {
        let edge_count = indices.len();
        if idxptr[0] != 0 {
            panic!("Bad index ptr!");
        }
        for index in idxptr.iter() {
            if *index >= edge_count {
                panic!("Bad index!");
            }
        }
        return SparseGraph { indices, idxptr };
    }

    pub fn scc(&self) -> (usize, [usize; N]) {
        let end = N + 1;
        let void = N + 2;

        let mut lowlinks: [usize; N] = [void; N];
        let mut stack_f: [usize; N] = [void; N];
        let mut stack_b: [usize; N] = [void; N];

        let mut label = N - 1;
        let mut index = 0;
        let mut ss_head = end;

        println!("{:?}", self);

        println!("lowlinks: {:?}", lowlinks);
        println!("stack_f: {:?}", stack_f);
        println!("stack_b: {:?}", stack_b);

        println!("label: {}", label);
        println!("index: {}", index);
        println!("ss_head: {}", ss_head);
        // Iterate over every node in order
        for v1 in 0..N {
            println!("\nv1: {:?}", v1);
            // If not node hasn't been processed yet, it won't have a lowlink or a label
            if lowlinks[v1] == void {
                println!("DFS PUSH: {}", v1);
                // DFS-stack push;
                // At this point, the DFS stack is empty, so pushing sets both the
                // forward and backwards pointers to end.
                let mut stack_head = v1;
                stack_f[v1] = end;
                stack_b[v1] = end;
                // We'll now proceed wih the inner loop algorithm until the stack is empty
                while stack_head != end {
                    let v = stack_head;
                    println!("  PROCESS STACK: {}", v);
                    println!("  lowlinks: {:?}", lowlinks);
                    if lowlinks[v] == void {
                        println!("    TRAVERSE");
                        // If the top node in the stack hasn't been visited yet,
                        // assign it the next index value.
                        lowlinks[v] = index;
                        index += 1;

                        // Visit all of the nodes accessible from v and push then onto the stack
                        // ahead of v. If they're already in the stack, bring them to the top.
                        let range_end = if v == N - 1 { N } else { self.idxptr[v + 1] };
                        for j in self.idxptr[v]..range_end {
                            let w = self.indices[j];
                            if lowlinks[w] == void {
                                if stack_f[w] != void {
                                    // w is already inside the stack, so excise it.
                                    let f = stack_f[w];
                                    let b = stack_b[w];
                                    if b != end {
                                        stack_f[b] = f;
                                    }
                                    if f != end {
                                        stack_b[f] = b;
                                    }
                                }

                                // Add w to the top of the stack. end <-> w <-> stack_head <-> ...
                                println!("      DFS PUSH: {}", w);
                                stack_f[w] = stack_head;
                                stack_b[w] = end;
                                stack_b[stack_head] = w;
                                stack_head = w;
                            }
                        }
                    } else {
                        println!("    POP");
                        // DFS-stack pop
                        stack_head = stack_f[v];
                        // If the stack_head isn't the end
                        if stack_head < N {
                            stack_b[stack_head] = end;
                        }
                        stack_f[v] = void;
                        stack_b[v] = void;

                        // Find out whether this node is a root node
                        // We look at all its linked nodes (which have now all had this
                        // process applied to them!). If none of them have a lower index than this
                        // node then we have a root value. Otherwise we reset the index to the lowest
                        // index.
                        let mut root = true;
                        let mut low_v = lowlinks[v];
                        println!("      low_v {}", low_v);
                        let range_end = if v == N - 1 { N } else { self.idxptr[v + 1] };
                        for j in self.idxptr[v]..range_end {
                            let low_w = lowlinks[self.indices[j]];
                            println!("      low_w {}", low_w);
                            if low_w < low_v {
                                low_v = low_w;
                                root = false;
                            }
                        }
                        lowlinks[v] = low_v;
                        let ss = &mut stack_f;
                        if root {
                            println!("      ROOT");
                            // Found a root node. This means we've found the root of
                            // a strongly connected component. All the items on the stack
                            // with an index greater or equal to the current nodes index
                            // are part of the SCC and get the same level.
                            // We can reclaim their index values at this point.

                            // while S not empty and rindex[v] <= rindex[top[S]]
                            while ss_head != end && lowlinks[v] <= lowlinks[ss_head] {
                                let w = ss_head; // w = pop(S)
                                ss_head = ss[w];
                                ss[w] = void;
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
                            println!("      DEC LABEL {}", label);
                            if label > 0 {
                                label -= 1;
                            }
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

        println!("END LABELS, {:?}", labels);

        for label in labels.iter_mut() {
            *label = (N - 1) - *label
        }
        println!("FINAL LABELS, {:?}", labels);
        return ((N - 1) - label, lowlinks);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sparse_graph_new() {
        let g = SparseGraph::new([0, 1, 2], vec![1, 2, 0]);
        assert_eq!(g.idxptr, [0, 1, 2]);
        assert_eq!(g.indices, [1, 2, 0]);
    }

    #[test]
    fn scc() {
        let g = SparseGraph::new([0, 1, 2], vec![1, 2, 0]);
        let (n, labels) = g.scc();
        assert_eq!(n, 1);
        assert_eq!(labels, [0, 0, 0]);
    }
}
