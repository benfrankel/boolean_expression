// boolean_expression: a Rust crate for Boolean expressions and BDDs.
//
// Copyright (c) 2016 Chris Fallin <cfallin@c1f.net>. Released under the MIT
// License.
//

use std::cmp;
use std::cmp::Ordering;
use std::collections::hash_map::Entry as HashEntry;
use std::collections::BTreeSet;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt;
use std::fmt::Debug;
use std::hash::Hash;

use itertools::Itertools;

use crate::cubes::Cube;
use crate::cubes::CubeList;
use crate::cubes::CubeVar;
use crate::idd::*;
use crate::Expr;

/// A `BddFunc` is a function index within a particular `Bdd`. It must only
/// be used with the `Bdd` instance which produced it.
pub type BddFunc = usize;

/// A special terminal `BddFunc` which is constant `false` (zero).
pub const BDD_ZERO: BddFunc = usize::MAX;
/// A special terminal `BddFunc` which is constant `true` (one).
pub const BDD_ONE: BddFunc = usize::MAX - 1;

pub(crate) type BddLabel = usize;

#[derive(Clone, PartialEq, Eq, Hash)]
pub(crate) struct BddNode {
    pub label: BddLabel,
    pub lo: BddFunc,
    pub hi: BddFunc,
    pub varcount: usize,
}

fn bdd_func_str(b: BddFunc) -> String {
    if b == BDD_ZERO {
        "ZERO".to_owned()
    } else if b == BDD_ONE {
        "ONE".to_owned()
    } else {
        format!("{}", b)
    }
}

impl Debug for BddNode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "BddNode(label = {}, lo = {}, hi = {})",
            self.label,
            bdd_func_str(self.lo),
            bdd_func_str(self.hi)
        )
    }
}

#[derive(Clone, Debug, Default)]
pub struct LabelBdd {
    pub(crate) nodes: Vec<BddNode>,
    dedup_hash: HashMap<BddNode, BddFunc>,
}

impl LabelBdd {
    pub fn new() -> LabelBdd {
        Self::default()
    }

    fn get_node(&mut self, label: BddLabel, lo: BddFunc, hi: BddFunc) -> BddFunc {
        if lo == hi {
            return lo;
        }
        let n = BddNode {
            label,
            lo,
            hi,
            varcount: cmp::min(self.sat_varcount(lo), self.sat_varcount(hi) + 1),
        };
        match self.dedup_hash.entry(n.clone()) {
            HashEntry::Occupied(o) => *o.get(),
            HashEntry::Vacant(v) => {
                let idx = self.nodes.len() as BddFunc;
                self.nodes.push(n);
                v.insert(idx);
                idx
            }
        }
    }

    fn sat_varcount(&self, f: BddFunc) -> usize {
        if f == BDD_ZERO || f == BDD_ONE {
            0
        } else {
            self.nodes[f].varcount
        }
    }

    pub fn terminal(&mut self, label: BddLabel) -> BddFunc {
        self.get_node(label, BDD_ZERO, BDD_ONE)
    }

    pub fn constant(&mut self, value: bool) -> BddFunc {
        if value {
            BDD_ONE
        } else {
            BDD_ZERO
        }
    }

    pub fn from_expr(&mut self, e: &Expr<BddLabel>) -> BddFunc {
        match e {
            &Expr::Terminal(t) => self.terminal(t),
            &Expr::Const(val) => self.constant(val),
            Expr::Not(x) => {
                let xval = self.from_expr(&*x);
                self.not(xval)
            }
            Expr::And(a, b) => {
                let aval = self.from_expr(&*a);
                let bval = self.from_expr(&*b);
                self.and(aval, bval)
            }
            Expr::Or(a, b) => {
                let aval = self.from_expr(&*a);
                let bval = self.from_expr(&*b);
                self.or(aval, bval)
            }
        }
    }

    /// Restrict: fundamental building block of logical combinators. Takes a
    /// Shannon cofactor: i.e., returns a new function based on `f` but with the
    /// given label forced to the given value.
    pub fn restrict(&mut self, f: BddFunc, label: BddLabel, val: bool) -> BddFunc {
        if f == BDD_ZERO {
            return BDD_ZERO;
        }
        if f == BDD_ONE {
            return BDD_ONE;
        }

        let node = self.nodes[f].clone();
        match label.cmp(&node.label) {
            Ordering::Less => f,
            Ordering::Equal => {
                if val {
                    node.hi
                } else {
                    node.lo
                }
            }
            Ordering::Greater => {
                let lo = self.restrict(node.lo, label, val);
                let hi = self.restrict(node.hi, label, val);
                self.get_node(node.label, lo, hi)
            }
        }
    }

    fn min_label(&self, f: BddFunc) -> Option<BddLabel> {
        if f == BDD_ZERO || f == BDD_ONE {
            None
        } else {
            Some(self.nodes[f].label)
        }
    }

    /// If-then-else: fundamental building block of logical combinators. Works
    /// by divide-and-conquer: split on the lowest appearing label, take Shannon
    /// cofactors for the two cases, recurse, and recombine with a new node.
    pub fn ite(&mut self, i: BddFunc, t: BddFunc, e: BddFunc) -> BddFunc {
        if i == BDD_ONE {
            t
        } else if i == BDD_ZERO {
            e
        } else if t == e {
            t
        } else if t == BDD_ONE && e == BDD_ZERO {
            i
        } else {
            let i_var = self.min_label(i).unwrap_or(usize::MAX);
            let t_var = self.min_label(t).unwrap_or(usize::MAX);
            let e_var = self.min_label(e).unwrap_or(usize::MAX);
            let split = cmp::min(i_var, cmp::min(t_var, e_var));
            assert_ne!(split, usize::MAX);
            let i_lo = self.restrict(i, split, false);
            let t_lo = self.restrict(t, split, false);
            let e_lo = self.restrict(e, split, false);
            let i_hi = self.restrict(i, split, true);
            let t_hi = self.restrict(t, split, true);
            let e_hi = self.restrict(e, split, true);
            let lo = self.ite(i_lo, t_lo, e_lo);
            let hi = self.ite(i_hi, t_hi, e_hi);
            self.get_node(split, lo, hi)
        }
    }

    pub fn not(&mut self, n: BddFunc) -> BddFunc {
        self.ite(n, BDD_ZERO, BDD_ONE)
    }

    pub fn and(&mut self, a: BddFunc, b: BddFunc) -> BddFunc {
        self.ite(a, b, BDD_ZERO)
    }

    pub fn or(&mut self, a: BddFunc, b: BddFunc) -> BddFunc {
        self.ite(a, BDD_ONE, b)
    }

    pub fn xor(&mut self, a: BddFunc, b: BddFunc) -> BddFunc {
        let not_b = self.not(b);
        self.ite(a, not_b, b)
    }

    pub fn implies(&mut self, a: BddFunc, b: BddFunc) -> BddFunc {
        let not_a = self.not(a);
        self.or(not_a, b)
    }

    pub fn evaluate(&self, func: BddFunc, inputs: &[bool]) -> Option<bool> {
        let mut f = func;
        for (i, val) in inputs.iter().enumerate() {
            if f == BDD_ZERO || f == BDD_ONE {
                break;
            }
            let node = &self.nodes[f];
            if node.label == i {
                f = if *val { node.hi } else { node.lo };
            }
        }
        match f {
            BDD_ZERO => Some(false),
            BDD_ONE => Some(true),
            _ => None,
        }
    }

    fn compute_cubelist(&self, memoize_vec: &mut Vec<Option<CubeList>>, n: BddFunc, nvars: usize) {
        if memoize_vec[n].is_some() {
            return;
        }
        let label = self.nodes[n].label;
        let lo = self.nodes[n].lo;
        let hi = self.nodes[n].hi;
        let lo_list = match lo {
            BDD_ZERO => CubeList::new(),
            BDD_ONE => {
                CubeList::from_list(&[Cube::true_cube(nvars)]).with_var(label, CubeVar::False)
            }
            _ => {
                self.compute_cubelist(memoize_vec, lo, nvars);
                memoize_vec[lo]
                    .as_ref()
                    .unwrap()
                    .with_var(label, CubeVar::False)
            }
        };
        let hi_list = match hi {
            BDD_ZERO => CubeList::new(),
            BDD_ONE => {
                CubeList::from_list(&[Cube::true_cube(nvars)]).with_var(label, CubeVar::True)
            }
            _ => {
                self.compute_cubelist(memoize_vec, hi, nvars);
                memoize_vec[hi]
                    .as_ref()
                    .unwrap()
                    .with_var(label, CubeVar::True)
            }
        };
        let new_list = lo_list.merge(&hi_list);
        memoize_vec[n] = Some(new_list);
    }

    fn cube_to_expr(&self, c: &Cube) -> Expr<BddLabel> {
        c.vars()
            .enumerate()
            .flat_map(|(i, v)| match v {
                CubeVar::False => Some(!Expr::Terminal(i)),
                CubeVar::True => Some(Expr::Terminal(i)),
                CubeVar::DontCare => None,
            })
            .reduce(Expr::and)
            .unwrap_or(Expr::Const(true))
    }

    fn cubelist_to_expr(&self, c: &CubeList) -> Expr<BddLabel> {
        c.cubes()
            .map(|c| self.cube_to_expr(c))
            .reduce(Expr::or)
            .unwrap_or(Expr::Const(false))
    }

    pub fn to_expr(&self, func: BddFunc, nvars: usize) -> Expr<BddLabel> {
        if func == BDD_ZERO {
            Expr::Const(false)
        } else if func == BDD_ONE {
            Expr::Const(true)
        } else {
            // At each node, we construct a cubelist, starting from the roots.
            let mut cubelists: Vec<Option<CubeList>> = Vec::with_capacity(self.nodes.len());
            cubelists.resize(self.nodes.len(), None);
            self.compute_cubelist(&mut cubelists, func, nvars);
            self.cubelist_to_expr(cubelists[func].as_ref().unwrap())
        }
    }

    /// Returns a function that is true whenever the maximum number of
    /// functions in `funcs` are true.
    pub fn max_sat(&mut self, funcs: &[BddFunc]) -> BddFunc {
        // First, construct an IDD function for each BDD function,
        // with value 1 if true and 0 if false. Then add these
        // together to obtain a single IDD function whose value is the
        // number of satisfied (true) BDD functions.
        let mut idd = LabelIdd::from_bdd(self);
        let satisfied_count = funcs
            .iter()
            .map(|f| IddFunc::from_bdd_func(*f))
            .reduce(|a, b| idd.add(a, b))
            .unwrap();

        // Now, find the maximum reachable count.
        let max_count = idd.max_value(satisfied_count.clone());

        // Finally, return a boolean function that is true when the
        // maximal number of functions are satisfied.
        let c = idd.constant(max_count);
        idd.eq(satisfied_count, c, self)
    }
}

/// A `Bdd` is a Binary Decision Diagram, an efficient way to represent a
/// Boolean function in a canonical way. (It is actually a "Reduced Ordered
/// Binary Decision Diagram", which gives it its canonicity assuming terminals
/// are ordered consistently.)
///
/// A BDD is built up from terminals (free variables) and constants, combined
/// with the logical combinators AND, OR, and NOT. It may be evaluated with
/// certain terminal assignments.
///
/// The major advantage of a BDD is that its logical operations are performed,
/// it will "self-simplify": i.e., taking the OR of `And(a, b)` and `And(a,
/// Not(b))` will produce `a` without any further simplification step. Furthermore,
/// the `BddFunc` representing this value is canonical: if two different
/// expressions are produced within the same BDD and they both result in
/// (simplify down to) `a`, then the `BddFunc` values will be equal. The
/// tradeoff is that logical operations may be expensive: they are linear in
/// BDD size, but BDDs may have exponential size (relative to terminal count)
/// in the worst case.
#[derive(Clone, Debug)]
pub struct Bdd<T> {
    bdd: LabelBdd,
    labels: HashMap<T, BddLabel>,
    rev_labels: Vec<T>,
}

impl<T> Default for Bdd<T> {
    fn default() -> Self {
        Self {
            bdd: Default::default(),
            labels: Default::default(),
            rev_labels: Default::default(),
        }
    }
}

impl<T> Bdd<T> {
    /// Produce a new, empty, BDD.
    pub fn new() -> Self {
        Self::default()
    }

    /// Produce a function within the BDD representing the constant value `val`.
    pub fn constant(&mut self, val: bool) -> BddFunc {
        self.bdd.constant(val)
    }

    /// Produce a function within the BDD representing the logical if-then-else
    /// of the functions `i`, `t`, and `e`
    pub fn ite(&mut self, i: BddFunc, t: BddFunc, e: BddFunc) -> BddFunc {
        self.bdd.ite(i, t, e)
    }

    /// Produce a function within the BDD representing the logical complement
    /// of the function `n`.
    pub fn not(&mut self, n: BddFunc) -> BddFunc {
        self.bdd.not(n)
    }

    /// Produce a function within the BDD representing the logical AND of the
    /// functions `a` and `b`.
    pub fn and(&mut self, a: BddFunc, b: BddFunc) -> BddFunc {
        self.bdd.and(a, b)
    }

    /// Produce a function within the BDD representing the logical OR of the
    /// functions `a` and `b`.
    pub fn or(&mut self, a: BddFunc, b: BddFunc) -> BddFunc {
        self.bdd.or(a, b)
    }

    /// Produce a function within the BDD representing the logical XOR of the
    /// functions `a` and `b`.
    pub fn xor(&mut self, a: BddFunc, b: BddFunc) -> BddFunc {
        self.bdd.xor(a, b)
    }

    /// Produce a function within the BDD representing the logical implication `a` -> `b`.
    pub fn implies(&mut self, a: BddFunc, b: BddFunc) -> BddFunc {
        self.bdd.implies(a, b)
    }

    /// Check whether the function `f` within the BDD is satisfiable.
    pub fn sat(&self, f: BddFunc) -> bool {
        f != BDD_ZERO
    }

    /// Produce an ordered set of nodes in the BDD function `f`: the transitive closure of
    /// reachable nodes.
    fn reachable_nodes(&self, f: BddFunc, s: &mut BTreeSet<BddFunc>) {
        if f != BDD_ZERO && f != BDD_ONE {
            // we use a BTreeSet instead of a HashSet since its order is stable.
            if s.insert(f) {
                self.reachable_nodes(self.bdd.nodes[f].hi, s);
                self.reachable_nodes(self.bdd.nodes[f].lo, s);
            }
        }
    }

    /// Produce a function that is true when the maximal number of
    /// given input functions are true.
    pub fn max_sat(&mut self, funcs: &[BddFunc]) -> BddFunc {
        self.bdd.max_sat(funcs)
    }

    /// Return an iterator over all labels in the BDD.
    pub fn labels(&self) -> impl Iterator<Item = &T> {
        self.labels.keys()
    }
}

impl<T: Clone> Bdd<T> {
    /// Convert the BDD to a minimized sum-of-products expression.
    pub fn to_expr(&self, f: BddFunc) -> Expr<T> {
        self.bdd
            .to_expr(f, self.rev_labels.len())
            .map(|t| self.rev_labels[*t].clone())
    }
}

impl<T: Debug> Bdd<T> {
    /// Export BDD to `dot` format (from the graphviz package) to enable visualization.
    pub fn to_dot(&self, f: BddFunc) -> String {
        // the algorithm starts at the f BDD function and then recursively collects all BddNodes
        // until BDD_ZERO and BDD_ONE. The output for each node is straightforward: just a single
        // `dot` node.
        let mut out = String::from("digraph bdd {\n");

        let mut nodes = BTreeSet::new();
        self.reachable_nodes(f, &mut nodes);
        for func in nodes {
            if func <= f {
                out.push_str(&format!(
                    "n{} [label = {:?}];\n",
                    func, self.rev_labels[self.bdd.nodes[func].label]
                ));
                out.push_str(&format!(
                    "n{} -> n{} [style=dotted];\n",
                    func, self.bdd.nodes[func].lo
                ));
                out.push_str(&format!("n{} -> n{};\n", func, self.bdd.nodes[func].hi));
            }
        }

        out.push_str(&format!("n{} [label=\"0\"];\n", BDD_ZERO));
        out.push_str(&format!("n{} [label=\"1\"];\n", BDD_ONE));

        out.push('}');

        out.to_string()
    }
}

impl<T: Eq + Hash> Bdd<T> {
    /// Return a new function based on `f` but with the given label forced to the given value.
    pub fn restrict(&mut self, f: BddFunc, t: T, val: bool) -> BddFunc {
        self.bdd.restrict(f, self.labels[&t], val)
    }

    /// Evaluate the function `f` in the BDD with the given terminal
    /// assignments. Any terminals not specified in `values` default to `false`.
    pub fn evaluate(&self, f: BddFunc, values: &HashMap<T, bool>) -> bool {
        let size = self.rev_labels.len();
        let mut valarray = Vec::with_capacity(size);
        valarray.resize(size, false);
        for (t, l) in &self.labels {
            valarray[*l] = *values.get(t).unwrap_or(&false);
        }
        self.bdd.evaluate(f, &valarray).unwrap()
    }
}

impl<T: Eq + Hash + Clone> Bdd<T> {
    fn label(&mut self, t: T) -> BddLabel {
        match self.labels.entry(t.clone()) {
            HashEntry::Occupied(o) => *o.get(),
            HashEntry::Vacant(v) => {
                let next_id = self.rev_labels.len() as BddLabel;
                v.insert(next_id);
                self.rev_labels.push(t);
                next_id
            }
        }
    }

    /// Produce a function within the BDD representing the terminal `t`. If
    /// this terminal has been used in the BDD before, the same `BddFunc` will be
    /// returned.
    pub fn terminal(&mut self, t: T) -> BddFunc {
        let l = self.label(t);
        self.bdd.terminal(l)
    }

    /// Compute an assignment for terminals which satisfies 'f'.  If
    /// satisfiable, this function returns a HashMap with the
    /// assignments (true, false) for terminals unless a terminal's
    /// assignment does not matter for satisfiability. If 'f' is not
    /// satisfiable, returns None.
    ///
    /// Example: for the boolean function "a or b", this function
    /// could return one of the following two HashMaps: {"a" -> true}
    /// or {"b" -> true}.
    pub fn sat_one(&self, f: BddFunc) -> Option<HashMap<T, bool>> {
        let mut h = HashMap::new();
        if self.sat_one_internal(f, &mut h) {
            Some(h)
        } else {
            None
        }
    }

    fn sat_one_internal(&self, f: BddFunc, assignments: &mut HashMap<T, bool>) -> bool {
        match f {
            BDD_ZERO => false,
            BDD_ONE => true,
            _ => {
                let hi = self.bdd.nodes[f].hi;
                let lo = self.bdd.nodes[f].lo;
                if hi != BDD_ZERO
                    && (lo == BDD_ZERO || self.bdd.sat_varcount(hi) < self.bdd.sat_varcount(lo))
                {
                    assignments.insert(self.rev_labels[self.bdd.nodes[f].label].clone(), true);
                    self.sat_one_internal(hi, assignments);
                } else {
                    assignments.insert(self.rev_labels[self.bdd.nodes[f].label].clone(), false);
                    self.sat_one_internal(lo, assignments);
                }
                true
            }
        }
    }

    /// Produce a function within the BDD representing the given expression
    /// `e`, which may contain ANDs, ORs, NOTs, terminals, and constants.
    pub fn from_expr(&mut self, e: &Expr<T>) -> BddFunc {
        match e {
            Expr::Terminal(t) => self.terminal(t.clone()),
            &Expr::Const(val) => self.constant(val),
            Expr::Not(x) => {
                let xval = self.from_expr(&*x);
                self.not(xval)
            }
            Expr::And(a, b) => {
                let aval = self.from_expr(&*a);
                let bval = self.from_expr(&*b);
                self.and(aval, bval)
            }
            Expr::Or(a, b) => {
                let aval = self.from_expr(&*a);
                let bval = self.from_expr(&*b);
                self.or(aval, bval)
            }
        }
    }
}

/// The `BddOutput` trait provides an interface to inform a listener about new
/// BDD nodes that are created. It allows the user to persist a BDD to a stream
/// (e.g., a log or trace file) as a long-running process executes. A
/// `BddOutput` instance may be provided to all BDD operations.
pub trait BddOutput<T, E> {
    fn write_label(&self, label: T, label_id: u64) -> Result<(), E>;
    fn write_node(
        &self,
        node_id: BddFunc,
        label_id: u64,
        lo: BddFunc,
        hi: BddFunc,
    ) -> Result<(), E>;
}

/// A `PersistedBdd` is a wrapper around a `Bdd` that provides a means to write
/// BDD labels and nodes out to a `BddOutput`. It tracks how much of the BDD
/// has already been writen out, and writes out new nodes and labels as
/// required when its `persist()` or `persist_all()` method is called.
pub struct PersistedBdd<T> {
    bdd: Bdd<T>,
    next_output_func: BddFunc,
    next_output_label: BddLabel,
}

impl<T> Default for PersistedBdd<T> {
    fn default() -> Self {
        Self {
            bdd: Default::default(),
            next_output_func: Default::default(),
            next_output_label: Default::default(),
        }
    }
}

impl<T> PersistedBdd<T> {
    /// Create a new `PersistedBdd`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Return the inner BDD.
    pub fn bdd(&self) -> &Bdd<T> {
        &self.bdd
    }

    /// Return the inner BDD.
    pub fn bdd_mut(&mut self) -> &mut Bdd<T> {
        &mut self.bdd
    }
}

impl<T: Clone> PersistedBdd<T> {
    /// Persist (at least) all labels and nodes in the BDD necessary to fully
    /// describe BDD function `f`. More records than strictly necessary may be
    /// written out.
    pub fn persist<E>(&mut self, f: BddFunc, out: &dyn BddOutput<T, E>) -> Result<(), E> {
        if f == BDD_ZERO || f == BDD_ONE {
            // No need to persist the terminal constant nodes!
            return Ok(());
        }
        while self.next_output_label < self.bdd.rev_labels.len() {
            let id = self.next_output_label;
            let t = self.bdd.rev_labels[id].clone();
            out.write_label(t, id as u64)?;
            self.next_output_label += 1;
        }
        while self.next_output_func <= f {
            let id = self.next_output_func;
            let node = &self.bdd.bdd.nodes[id];
            out.write_node(id, node.label as u64, node.lo, node.hi)?;
            self.next_output_func += 1;
        }
        Ok(())
    }

    /// Persist all labels and nodes in the BDD.
    pub fn persist_all<E>(&mut self, out: &dyn BddOutput<T, E>) -> Result<(), E> {
        if !self.bdd.bdd.nodes.is_empty() {
            let last_f = self.bdd.bdd.nodes.len() - 1;
            self.persist(last_f, out)
        } else {
            Ok(())
        }
    }
}

/// A `BddLoader` provides a way to inject BDD nodes directly, as they were
/// previously dumped by a `PersistedBdd` to a `BddOutput`. The user should
/// create a `BddLoader` instance wrapped around a `Bdd` and call
/// `inject_label` and `inject_node` as appropriate to inject labels and nodes.
pub struct BddLoader<'a, T> {
    bdd: &'a mut Bdd<T>,
}

impl<'a, T> BddLoader<'a, T> {
    /// Create a new `BddLoader` wrapping the given `Bdd`. The `BddLoader`
    /// holds a mutable reference to `bdd` until destroyed. `bdd` must be empty
    /// initially.
    pub fn new(bdd: &'a mut Bdd<T>) -> Self {
        assert_eq!(bdd.labels.len(), 0);
        assert_eq!(bdd.rev_labels.len(), 0);
        assert_eq!(bdd.bdd.nodes.len(), 0);
        Self { bdd }
    }

    /// Inject a new node into the BDD. The `id` must be the next consecutive
    /// `id`; i.e., nodes must be injected in the order they were dumped to a
    /// `BddOutput`.
    pub fn inject_node(&mut self, id: BddFunc, label_id: u64, lo: BddFunc, hi: BddFunc) {
        assert_eq!(id, self.bdd.bdd.nodes.len() as BddFunc);
        let n = BddNode {
            label: label_id as BddLabel,
            lo,
            hi,
            varcount: cmp::min(
                self.bdd.bdd.sat_varcount(lo),
                self.bdd.bdd.sat_varcount(hi) + 1,
            ),
        };
        self.bdd.bdd.nodes.push(n.clone());
        self.bdd.bdd.dedup_hash.insert(n, id);
    }
}

impl<'a, T: Eq + Hash + Clone> BddLoader<'a, T> {
    /// Inject a new label into the BDD. The `id` must be the next consecutive
    /// `id`; i.e., labels must be injected in the order they were dumped to a
    /// `BddOutput`.
    pub fn inject_label(&mut self, t: T, id: u64) {
        assert_eq!(id, self.bdd.rev_labels.len() as u64);
        self.bdd.rev_labels.push(t.clone());
        self.bdd.labels.insert(t, id as BddLabel);
    }
}

#[cfg(test)]
mod test {
    use std::cell::RefCell;
    use std::collections::HashMap;

    use indoc::indoc;
    use rand::Rng;
    use rand::SeedableRng;
    use rand_xorshift::XorShiftRng;

    use super::*;

    fn term_hashmap(vals: &[bool], h: &mut HashMap<u32, bool>) {
        h.clear();
        for (i, v) in vals.iter().enumerate() {
            h.insert(i as u32, *v);
        }
    }

    fn test_bdd(
        b: &Bdd<u32>,
        f: BddFunc,
        h: &mut HashMap<u32, bool>,
        inputs: &[bool],
        expected: bool,
    ) {
        term_hashmap(inputs, h);
        assert_eq!(b.evaluate(f, h), expected);
    }

    #[test]
    fn bdd_eval() {
        let mut h = HashMap::new();
        let mut b = Bdd::new();
        let expr = Expr::or(
            Expr::and(Expr::Terminal(0), Expr::Terminal(1)),
            Expr::and(!Expr::Terminal(2), !Expr::Terminal(3)),
        );
        let f = b.from_expr(&expr);
        test_bdd(&b, f, &mut h, &[false, false, true, true], false);
        test_bdd(&b, f, &mut h, &[true, false, true, true], false);
        test_bdd(&b, f, &mut h, &[true, true, true, true], true);
        test_bdd(&b, f, &mut h, &[false, false, false, true], false);
        test_bdd(&b, f, &mut h, &[false, false, false, false], true);
    }

    fn bits_to_hashmap(bits: usize, n: usize, h: &mut HashMap<u32, bool>) {
        for b in 0..bits {
            h.insert(b as u32, (n & (1 << b)) != 0);
        }
    }

    fn test_bdd_expr(e: Expr<u32>, nterminals: usize) {
        let mut b = Bdd::new();
        let f = b.from_expr(&e);
        let mut terminal_values = HashMap::new();
        let mut expected_satisfiable = false;
        for v in 0..(1 << nterminals) {
            bits_to_hashmap(nterminals, v, &mut terminal_values);
            let expr_val = e.evaluate(&terminal_values);
            let bdd_val = b.evaluate(f, &terminal_values);
            assert_eq!(expr_val, bdd_val);
            if expr_val {
                expected_satisfiable = true;
            }
        }
        // test sat_one
        let sat_result = b.sat_one(f);
        assert_eq!(sat_result.is_some(), expected_satisfiable);
        if expected_satisfiable {
            assert!(b.evaluate(f, &sat_result.unwrap()));
        }
    }

    fn random_expr<R: Rng>(r: &mut R, nterminals: usize) -> Expr<u32> {
        match r.gen_range(0..=4) {
            0 => Expr::Terminal(r.gen_range(0..nterminals) as u32),
            1 => Expr::Const(r.gen::<bool>()),
            2 => Expr::Not(Box::new(random_expr(r, nterminals))),
            3 => Expr::And(
                Box::new(random_expr(r, nterminals)),
                Box::new(random_expr(r, nterminals)),
            ),
            4 => Expr::Or(
                Box::new(random_expr(r, nterminals)),
                Box::new(random_expr(r, nterminals)),
            ),
            _ => unreachable!(),
        }
    }

    #[test]
    fn bdd_exhaustive_exprs() {
        let mut rng = XorShiftRng::from_seed(rand::thread_rng().gen());
        for _ in 0..100 {
            let expr = random_expr(&mut rng, 6);
            test_bdd_expr(expr, 6);
        }
    }

    #[test]
    fn bdd_to_expr() {
        let mut b = Bdd::new();
        let f_true = b.constant(true);
        assert_eq!(b.to_expr(f_true), Expr::Const(true));
        let f_false = b.constant(false);
        assert_eq!(b.to_expr(f_false), Expr::Const(false));
        let f_0 = b.terminal(0);
        let f_1 = b.terminal(1);
        let f_and = b.and(f_0, f_1);
        assert_eq!(
            b.to_expr(f_and),
            Expr::and(Expr::Terminal(0), Expr::Terminal(1))
        );
        let f_or = b.or(f_0, f_1);
        assert_eq!(
            b.to_expr(f_or),
            Expr::or(Expr::Terminal(1), Expr::Terminal(0))
        );
        let f_not = b.not(f_0);
        assert_eq!(b.to_expr(f_not), !Expr::Terminal(0));
        let f_2 = b.terminal(2);
        let f_1_or_2 = b.or(f_1, f_2);
        let f_0_and_1_or_2 = b.and(f_0, f_1_or_2);
        assert_eq!(
            b.to_expr(f_0_and_1_or_2),
            Expr::or(
                Expr::and(Expr::Terminal(0), Expr::Terminal(2)),
                Expr::and(Expr::Terminal(0), Expr::Terminal(1)),
            ),
        );
    }

    #[derive(Clone, Debug)]
    struct InMemoryBddLog {
        labels: RefCell<Vec<(u64, String)>>,
        nodes: RefCell<Vec<(BddFunc, u64, BddFunc, BddFunc)>>,
    }

    impl InMemoryBddLog {
        pub fn new() -> InMemoryBddLog {
            InMemoryBddLog {
                labels: RefCell::new(Vec::new()),
                nodes: RefCell::new(Vec::new()),
            }
        }
    }

    impl BddOutput<String, ()> for InMemoryBddLog {
        fn write_label(&self, l: String, label_id: u64) -> Result<(), ()> {
            let mut labels = self.labels.borrow_mut();
            labels.push((label_id, l));
            Ok(())
        }

        fn write_node(
            &self,
            node_id: BddFunc,
            label_id: u64,
            lo: BddFunc,
            hi: BddFunc,
        ) -> Result<(), ()> {
            let mut nodes = self.nodes.borrow_mut();
            nodes.push((node_id, label_id, lo, hi));
            Ok(())
        }
    }

    #[test]
    // the tests compare the dot output to a string which has been manually verified to be correct
    fn dot_output() {
        let mut bdd = Bdd::new();
        let a = bdd.terminal("a");
        let b = bdd.terminal("b");
        let b_and_a = bdd.and(a, b);
        {
            let dot = bdd.to_dot(b_and_a);
            assert_eq!(
                dot,
                indoc!(
                    "
                            digraph bdd {
                            n1 [label = \"b\"];
                            n1 -> n18446744073709551615 [style=dotted];
                            n1 -> n18446744073709551614;
                            n2 [label = \"a\"];
                            n2 -> n18446744073709551615 [style=dotted];
                            n2 -> n1;
                            n18446744073709551615 [label=\"0\"];
                            n18446744073709551614 [label=\"1\"];
                            }"
                )
            );
        }
        let c = bdd.terminal("c");
        let c_or_a = bdd.or(c, a);
        {
            let dot = bdd.to_dot(c_or_a);
            assert_eq!(
                dot,
                indoc!(
                    "
                            digraph bdd {
                            n3 [label = \"c\"];
                            n3 -> n18446744073709551615 [style=dotted];
                            n3 -> n18446744073709551614;
                            n4 [label = \"a\"];
                            n4 -> n3 [style=dotted];
                            n4 -> n18446744073709551614;
                            n18446744073709551615 [label=\"0\"];
                            n18446744073709551614 [label=\"1\"];
                            }"
                )
            );
        }
        let not_c_and_b = bdd.not(b_and_a);
        let c_or_a_and_not_b_and_a = bdd.and(c_or_a, not_c_and_b);
        {
            let dot = bdd.to_dot(c_or_a_and_not_b_and_a);
            assert_eq!(
                dot,
                indoc!(
                    "
                            digraph bdd {
                            n3 [label = \"c\"];
                            n3 -> n18446744073709551615 [style=dotted];
                            n3 -> n18446744073709551614;
                            n5 [label = \"b\"];
                            n5 -> n18446744073709551614 [style=dotted];
                            n5 -> n18446744073709551615;
                            n7 [label = \"a\"];
                            n7 -> n3 [style=dotted];
                            n7 -> n5;
                            n18446744073709551615 [label=\"0\"];
                            n18446744073709551614 [label=\"1\"];
                            }"
                )
            );
        }
        {
            let new_a = bdd.terminal("a");
            let d = bdd.terminal("d");
            let new_a_or_d = bdd.or(new_a, d);
            let dot = bdd.to_dot(new_a_or_d);
            assert_eq!(
                dot,
                indoc!(
                    "
                            digraph bdd {
                            n8 [label = \"d\"];
                            n8 -> n18446744073709551615 [style=dotted];
                            n8 -> n18446744073709551614;
                            n9 [label = \"a\"];
                            n9 -> n8 [style=dotted];
                            n9 -> n18446744073709551614;
                            n18446744073709551615 [label=\"0\"];
                            n18446744073709551614 [label=\"1\"];
                            }"
                )
            );
        }
    }

    #[test]
    fn sat_one() {
        let mut bdd = Bdd::new();

        // empty BDDs
        assert!(bdd.sat_one(BDD_ONE).is_some());
        assert!(bdd.sat_one(BDD_ZERO).is_none());

        let a = bdd.terminal("a");
        let b = bdd.terminal("b");
        let b_and_a = bdd.and(a, b);
        let result = bdd.sat_one(b_and_a);
        assert!(result.is_some());
        assert!(bdd.evaluate(b_and_a, &result.unwrap()));

        let c = bdd.terminal("c");
        let not_c = bdd.not(c);
        let b_and_a_or_not_c = bdd.or(b_and_a, not_c);
        let result = bdd.sat_one(b_and_a_or_not_c);
        assert!(result.is_some());
        assert!(bdd.evaluate(b_and_a_or_not_c, &result.unwrap()));

        // unsatisfiable formula
        let c_and_not_c = bdd.and(c, not_c);
        assert!(bdd.sat_one(c_and_not_c).is_none());
    }

    #[test]
    fn max_sat() {
        let mut bdd = Bdd::new();
        // Test: a, a+b, a+c, c', c, bd, ad, d'
        let a = bdd.terminal(0);
        let b = bdd.terminal(1);
        let c = bdd.terminal(2);
        let d = bdd.terminal(3);
        let cnot = bdd.not(c);
        let dnot = bdd.not(d);
        let ab = bdd.and(a, b);
        let ac = bdd.and(a, c);
        let bd = bdd.and(b, d);
        let ad = bdd.and(a, d);
        let max_sat = bdd.max_sat(&[a, ab, ac, cnot, c, bd, ad, dnot]);
        let abc = bdd.and(ab, c);
        let abcd = bdd.and(abc, d);
        assert_eq!(max_sat, abcd);
    }

    #[test]
    fn max_sat_min_var() {
        let mut bdd = Bdd::new();
        // Test: a, a+b, a+c, c', c, bd, d'
        let a = bdd.terminal(0);
        let b = bdd.terminal(1);
        let c = bdd.terminal(2);
        let d = bdd.terminal(3);
        let cnot = bdd.not(c);
        let dnot = bdd.not(d);
        let ab = bdd.and(a, b);
        let ac = bdd.and(a, c);
        let bd = bdd.and(b, d);
        let max_sat = bdd.max_sat(&[a, ab, ac, cnot, c, bd, dnot]);
        let abc = bdd.and(ab, c);
        assert_eq!(max_sat, abc);
        let assn = bdd.sat_one(max_sat).unwrap();
        assert_eq!(assn.get(&0), Some(&true));
        assert_eq!(assn.get(&1), Some(&true));
        assert_eq!(assn.get(&2), Some(&true));
        assert_eq!(assn.get(&3), None);
    }

    #[test]
    fn persist_bdd() {
        let out = InMemoryBddLog::new();
        let mut p = PersistedBdd::new();
        let term_a = p.bdd_mut().terminal("A".to_owned());
        let term_b = p.bdd_mut().terminal("B".to_owned());
        let term_c = p.bdd_mut().terminal("C".to_owned());
        let ab = p.bdd_mut().and(term_a, term_b);
        let ab_or_c = p.bdd_mut().or(ab, term_c);
        p.persist(ab_or_c, &out).unwrap();
        assert_eq!(
            *out.labels.borrow(),
            vec![
                (0, "A".to_owned()),
                (1, "B".to_owned()),
                (2, "C".to_owned()),
            ],
        );
        assert_eq!(
            *out.nodes.borrow(),
            vec![
                (0, 0, BDD_ZERO, BDD_ONE),
                (1, 1, BDD_ZERO, BDD_ONE),
                (2, 2, BDD_ZERO, BDD_ONE),
                (3, 0, BDD_ZERO, 1),
                (4, 1, 2, BDD_ONE),
                (5, 0, 2, 4),
            ],
        );
    }

    #[test]
    fn load_bdd() {
        let mut bdd = Bdd::new();
        {
            let mut loader = BddLoader::new(&mut bdd);
            loader.inject_label("A".to_owned(), 0);
            loader.inject_label("B".to_owned(), 1);
            loader.inject_node(0, 1, BDD_ZERO, BDD_ONE);
            loader.inject_node(1, 0, BDD_ZERO, 0);
        }
        let mut h = HashMap::new();
        h.insert("A".to_owned(), true);
        h.insert("B".to_owned(), true);
        assert_eq!(bdd.evaluate(1, &h), true);
    }

    #[test]
    fn persist_empty_bdd() {
        let out = InMemoryBddLog::new();
        let mut p = PersistedBdd::new();
        p.persist(BDD_ZERO, &out).unwrap();
    }
}
