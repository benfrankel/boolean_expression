// boolean_expression: a Rust crate for Boolean expressions and BDDs.
//
// Copyright (c) 2016-2018 Chris Fallin <cfallin@c1f.net>. Released under the MIT
// License.
//

use std::cmp;
use std::cmp::Ordering;
use std::fmt;

use hashbrown::hash_map::Entry as HashEntry;
use hashbrown::HashMap;
use hashbrown::HashSet;

use crate::BddFunc;
use crate::BddLabel;
use crate::LabelBdd;
use crate::BDD_ONE;
use crate::BDD_ZERO;

#[derive(Clone, Debug, Hash, PartialOrd, Ord, PartialEq, Eq)]
pub(crate) enum IddFunc {
    Const(isize),
    Node(usize),
}

#[derive(Clone, Hash, PartialOrd, Ord, PartialEq, Eq)]
pub(crate) struct IddNode {
    label: BddLabel,
    lo: IddFunc,
    hi: IddFunc,
    max: isize,
}

impl fmt::Debug for IddNode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "IddNode(label = {}, lo = {:?}, hi = {:?}, max = {})",
            self.label, self.lo, self.hi, self.max
        )
    }
}

#[derive(Clone, Default)]
pub(crate) struct LabelIdd {
    nodes: Vec<IddNode>,
    dedup_hash: HashMap<IddNode, usize>,
}

impl fmt::Debug for LabelIdd {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "LabelIdd:")?;
        for (idx, node) in self.nodes.iter().enumerate() {
            writeln!(f, "  node {}: {:?}", idx, node)?;
        }
        Ok(())
    }
}

impl IddFunc {
    pub(crate) fn from_bdd_func(f: BddFunc) -> Self {
        if f == BDD_ZERO {
            Self::Const(0)
        } else if f == BDD_ONE {
            Self::Const(1)
        } else {
            Self::Node(f)
        }
    }

    pub fn as_const(&self) -> Option<isize> {
        match self {
            &Self::Const(i) => Some(i),
            _ => None,
        }
    }

    pub fn is_const(&self) -> bool {
        self.as_const().is_some()
    }

    pub fn as_node_idx(&self) -> Option<usize> {
        match self {
            &Self::Node(i) => Some(i),
            _ => None,
        }
    }

    pub fn is_node_idx(&self) -> bool {
        self.as_node_idx().is_some()
    }
}

impl LabelIdd {
    pub fn new() -> Self {
        Self::default()
    }

    pub(crate) fn from_bdd(bdd: &LabelBdd) -> Self {
        let mut l = Self::new();
        for n in &bdd.nodes {
            let lo = IddFunc::from_bdd_func(n.lo);
            let hi = IddFunc::from_bdd_func(n.hi);
            let label = n.label;
            let n = IddNode {
                label,
                lo: lo.clone(),
                hi: hi.clone(),
                max: cmp::max(l.max_value(lo.clone()), l.max_value(hi.clone())),
            };
            let this = l.nodes.len();
            l.dedup_hash.insert(n.clone(), this);
            l.nodes.push(n);
        }
        l
    }

    fn get_node(&mut self, label: BddLabel, lo: IddFunc, hi: IddFunc) -> IddFunc {
        if lo == hi {
            return lo;
        }
        let n = IddNode {
            label,
            lo: lo.clone(),
            hi: hi.clone(),
            max: cmp::max(self.max_value(lo), self.max_value(hi)),
        };
        match self.dedup_hash.entry(n.clone()) {
            HashEntry::Occupied(o) => IddFunc::Node(*o.get()),
            HashEntry::Vacant(v) => {
                let f = self.nodes.len();
                self.nodes.push(n);
                v.insert(f);
                IddFunc::Node(f)
            }
        }
    }

    pub fn terminal(&mut self, label: BddLabel, lo_val: isize, hi_val: isize) -> IddFunc {
        self.get_node(label, IddFunc::Const(lo_val), IddFunc::Const(hi_val))
    }

    pub fn constant(&mut self, i: isize) -> IddFunc {
        IddFunc::Const(i)
    }

    fn arith_op<F>(&mut self, a: IddFunc, b: IddFunc, f: &F) -> IddFunc
    where
        F: Fn(isize, isize) -> isize,
    {
        match (a.is_const(), b.is_const()) {
            (true, true) => self.constant(f(a.as_const().unwrap(), b.as_const().unwrap())),
            (false, true) => {
                let n = self.nodes[a.as_node_idx().unwrap()].clone();
                let add_lo = self.arith_op(n.lo.clone(), b.clone(), f);
                let add_hi = self.arith_op(n.hi.clone(), b, f);
                self.get_node(n.label, add_lo, add_hi)
            }
            (true, false) => {
                let n = self.nodes[b.as_node_idx().unwrap()].clone();
                let add_lo = self.arith_op(a.clone(), n.lo.clone(), f);
                let add_hi = self.arith_op(a, n.hi.clone(), f);
                self.get_node(n.label, add_lo, add_hi)
            }
            (false, false) => {
                assert!(a.is_node_idx() && b.is_node_idx());
                let n1 = self.nodes[a.as_node_idx().unwrap()].clone();
                let n2 = self.nodes[b.as_node_idx().unwrap()].clone();
                match n1.label.cmp(&n2.label) {
                    Ordering::Less => {
                        let add_lo = self.arith_op(n1.lo.clone(), b.clone(), f);
                        let add_hi = self.arith_op(n1.hi.clone(), b, f);
                        self.get_node(n1.label, add_lo, add_hi)
                    }
                    Ordering::Greater => {
                        let add_lo = self.arith_op(a.clone(), n2.lo.clone(), f);
                        let add_hi = self.arith_op(a, n2.hi.clone(), f);
                        self.get_node(n2.label, add_lo, add_hi)
                    }
                    Ordering::Equal => {
                        assert_eq!(n1.label, n2.label);
                        let add_lo = self.arith_op(n1.lo.clone(), n2.lo.clone(), f);
                        let add_hi = self.arith_op(n1.hi.clone(), n2.hi, f);
                        self.get_node(n1.label, add_lo, add_hi)
                    }
                }
            }
        }
    }

    pub fn add(&mut self, a: IddFunc, b: IddFunc) -> IddFunc {
        self.arith_op(a, b, &|aconst, bconst| aconst + bconst)
    }

    pub fn sub(&mut self, a: IddFunc, b: IddFunc) -> IddFunc {
        self.arith_op(a, b, &|aconst, bconst| aconst - bconst)
    }

    pub fn min(&mut self, a: IddFunc, b: IddFunc) -> IddFunc {
        self.arith_op(a, b, &cmp::min)
    }

    pub fn max(&mut self, a: IddFunc, b: IddFunc) -> IddFunc {
        self.arith_op(a, b, &cmp::max)
    }

    pub fn eq(&self, a: IddFunc, b: IddFunc, bdd: &mut LabelBdd) -> BddFunc {
        if a.is_const() && b.is_const() {
            if a.as_const().unwrap() == b.as_const().unwrap() {
                BDD_ONE
            } else {
                BDD_ZERO
            }
        } else if a.is_node_idx() {
            let n = self.nodes[a.as_node_idx().unwrap()].clone();
            let x0 = bdd.terminal(n.label);
            let eq_lo = self.eq(n.lo.clone(), b.clone(), bdd);
            let eq_hi = self.eq(n.hi, b, bdd);
            bdd.ite(x0, eq_hi, eq_lo)
        } else {
            self.eq(b, a, bdd)
        }
    }

    pub fn evaluate(&self, func: IddFunc, inputs: &[bool]) -> Option<isize> {
        if func.is_const() {
            return Some(func.as_const().unwrap());
        }

        let mut f = func;
        for (i, val) in inputs.iter().enumerate() {
            if f.is_const() {
                break;
            }
            let node = &self.nodes[f.as_node_idx().unwrap()];
            if node.label == i {
                f = if *val {
                    node.hi.clone()
                } else {
                    node.lo.clone()
                };
            }
        }
        f.as_const()
    }

    pub fn max_value(&self, f: IddFunc) -> isize {
        match f {
            IddFunc::Const(i) => i,
            IddFunc::Node(idx) => self.nodes[idx].max,
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_idd_const() {
        let mut idd = LabelIdd::new();
        let c0 = idd.constant(0);
        let c1 = idd.constant(1);
        let c2 = idd.constant(2);

        assert_eq!(idd.evaluate(c0.clone(), &[]), Some(0));
        assert_eq!(idd.evaluate(c1.clone(), &[]), Some(1));
        assert_eq!(idd.evaluate(c2.clone(), &[]), Some(2));

        let c3a = idd.add(c1.clone(), c2.clone());
        let c3b = idd.add(c2.clone(), c1.clone());
        let c2a = idd.add(c1.clone(), c1.clone());
        let c5 = idd.add(c3a.clone(), c2a.clone());

        assert_eq!(idd.evaluate(c3a.clone(), &[]), Some(3));
        assert_eq!(idd.evaluate(c3b.clone(), &[]), Some(3));
        assert_eq!(idd.evaluate(c2a.clone(), &[]), Some(2));
        assert_eq!(idd.evaluate(c5.clone(), &[]), Some(5));
    }

    #[test]
    fn test_idd_term() {
        let mut idd = LabelIdd::new();
        let x0 = idd.terminal(0, 10, 20);
        let x1 = idd.terminal(1, 35, 40);
        let x2 = idd.add(x0.clone(), x1.clone());
        let x3 = idd.sub(x0.clone(), x1.clone());
        let x4 = idd.min(x0.clone(), x1.clone());
        let x5 = idd.max(x0.clone(), x1.clone());

        assert_eq!(idd.evaluate(x2.clone(), &[false, false]), Some(45));
        assert_eq!(idd.evaluate(x2.clone(), &[false, true]), Some(50));
        assert_eq!(idd.evaluate(x2.clone(), &[true, false]), Some(55));
        assert_eq!(idd.evaluate(x2.clone(), &[true, true]), Some(60));

        assert_eq!(idd.evaluate(x3.clone(), &[false, false]), Some(-25));
        assert_eq!(idd.evaluate(x3.clone(), &[false, true]), Some(-30));
        assert_eq!(idd.evaluate(x3.clone(), &[true, false]), Some(-15));
        assert_eq!(idd.evaluate(x3.clone(), &[true, true]), Some(-20));

        assert_eq!(idd.evaluate(x4.clone(), &[false, false]), Some(10));
        assert_eq!(idd.evaluate(x4.clone(), &[false, true]), Some(10));
        assert_eq!(idd.evaluate(x4.clone(), &[true, false]), Some(20));
        assert_eq!(idd.evaluate(x4.clone(), &[true, true]), Some(20));

        assert_eq!(idd.evaluate(x5.clone(), &[false, false]), Some(35));
        assert_eq!(idd.evaluate(x5.clone(), &[false, true]), Some(40));
        assert_eq!(idd.evaluate(x5.clone(), &[true, false]), Some(35));
        assert_eq!(idd.evaluate(x5.clone(), &[true, true]), Some(40));

        assert_eq!(idd.evaluate(x4.clone(), &[true]), Some(20));
        assert_eq!(idd.evaluate(x5.clone(), &[true]), None);
    }

    #[test]
    fn test_idd_from_bdd() {
        let mut bdd = LabelBdd::new();
        let x0_bdd = bdd.terminal(0);
        let x1_bdd = bdd.terminal(1);
        let x2_bdd = bdd.and(x0_bdd, x1_bdd);
        let x3_bdd = bdd.not(x1_bdd);
        let x4_bdd = bdd.or(x2_bdd, x3_bdd);
        let idd = LabelIdd::from_bdd(&bdd);
        assert_eq!(
            idd.evaluate(IddFunc::from_bdd_func(x4_bdd), &[true, false]),
            Some(1),
        );
        assert_eq!(
            idd.evaluate(IddFunc::from_bdd_func(x4_bdd), &[false, false]),
            Some(1),
        );
        assert_eq!(
            idd.evaluate(IddFunc::from_bdd_func(x4_bdd), &[false, true]),
            Some(0),
        );
    }

    #[test]
    fn test_idd_max_value() {
        let mut idd = LabelIdd::new();
        let x0 = idd.terminal(0, 10, 20);
        let x1 = idd.terminal(1, 35, 40);
        let x2 = idd.add(x0.clone(), x1.clone());
        let x3 = idd.sub(x0.clone(), x1.clone());
        let x4 = idd.min(x0.clone(), x1.clone());
        let x5 = idd.max(x0.clone(), x1.clone());
        assert_eq!(idd.max_value(x0), 20);
        assert_eq!(idd.max_value(x1), 40);
        assert_eq!(idd.max_value(x2), 60);
        assert_eq!(idd.max_value(x3), -15);
        assert_eq!(idd.max_value(x4), 20);
        assert_eq!(idd.max_value(x5), 40);
    }

    #[test]
    fn test_idd_eq() {
        let mut idd = LabelIdd::new();
        let x0 = idd.terminal(0, 10, 20);
        let x1 = idd.terminal(1, 35, 40);
        let x2 = idd.add(x0.clone(), x1.clone());
        let x3 = idd.min(x0.clone(), x1.clone());
        let mut bdd = LabelBdd::new();
        let eq0 = idd.eq(x3.clone(), x0.clone(), &mut bdd);
        assert_eq!(eq0, BDD_ONE);
        let const45 = idd.constant(45);
        let eq1 = idd.eq(x2.clone(), const45, &mut bdd);
        assert_eq!(bdd.evaluate(eq1, &[false, false]), Some(true));
        assert_eq!(bdd.evaluate(eq1, &[false, true]), Some(false));
        assert_eq!(bdd.evaluate(eq1, &[true]), Some(false));
    }
}
