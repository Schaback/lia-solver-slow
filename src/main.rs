mod graph;

use crate::graph::render_graph;
use graph::Node;
use rug::ops::DivRounding;
use rug::{Assign, Integer};
use std::fmt::{self, Debug};
use std::path::PathBuf;
use std::str::FromStr;
use std::{collections::HashMap, fmt::Display, ops::Not};
use structopt::StructOpt;

#[derive(Debug, StructOpt)]
#[structopt(name = "lia-solver", about = "Solve LIA systems")]
struct Opt {
    /// Activate debug mode
    #[structopt(long)]
    debug: bool,

    /// Dumps dependency graph in DOT format
    #[structopt(long)]
    dump_dot: bool,

    /// Prints solution
    #[structopt(short, long)]
    print: bool,

    /// Input file
    #[structopt(parse(from_os_str))]
    input: PathBuf,
}

#[derive(Clone)]
struct Equation {
    coeff: Vec<Integer>,
    rhs: Integer,
}

impl Equation {
    fn with_coeff_count(num_vars: usize) -> Self {
        Equation {
            coeff: vec![Integer::new(); num_vars],
            rhs: Integer::new(),
        }
    }

    fn invert_coeff(&mut self) {
        for c in self.coeff.iter_mut() {
            *c *= -1;
        }
    }
}

impl Debug for Equation {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(fmt, "{}", self.rhs.to_string())?;
        for cff in self.coeff.iter() {
            write!(fmt, " {:>7}", cff.to_string())?;
        }
        write!(fmt, "")
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy, Ord, PartialOrd)]
struct VarName {
    name: usize,
    iter: usize,
}

impl Node for VarName {}

impl Display for VarName {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(fmt, "{}-{}", self.name, self.iter)
    }
}

#[derive(Debug)]
struct ResolveEquation {
    eqn: Equation,
    names: Vec<VarName>,
}

#[derive(Debug)]
struct System {
    equations: Vec<Equation>,
    orig_equations: Vec<Equation>,
    var_names: Vec<VarName>,
    sc_val: Integer,
    sc_eqn: usize,
    sc_cff: usize,
    num_vars: usize,
    replaced_by: HashMap<VarName, ResolveEquation>,
    first_replaced: Option<VarName>,
}

impl System {
    fn gcd_z(a: &mut Integer, b: &Integer) {
        if a == &Integer::ZERO {
            a.assign(b);
        } else if b == &Integer::ZERO {
            return;
        } else {
            a.gcd_mut(&b);
        }
    }

    fn mod_p(a: &mut Integer, b: &Integer) {
        let mut sub = a.clone();
        sub *= 2_i32;
        sub += b;
        sub = sub.div_euc(Integer::from(2_i32 * b));
        sub *= b;
        *a -= sub;
    }

    fn new(equations: Vec<Equation>, _num_eqs: usize, num_vars: usize) -> Self {
        System {
            equations: equations.clone(),
            orig_equations: equations,
            var_names: (0..num_vars)
                .map(|name| VarName { name, iter: 0 })
                .collect(),
            sc_val: Integer::from(u128::MAX), //TODO
            sc_eqn: 0,
            sc_cff: 0,
            num_vars,
            replaced_by: HashMap::new(),
            first_replaced: None,
        }
    }

    fn solvable(&mut self) -> bool {
        self.sc_val = Integer::from(u128::MAX); //TODO
        let mut del_idx = Vec::new();
        let res = self
            .equations
            .iter_mut()
            .enumerate()
            .map(|(idx, Equation { coeff, rhs })| {
                // Calculate the GCD
                let gcd = coeff.iter().fold(Integer::new(), |mut x, y| {
                    System::gcd_z(&mut x, y);
                    x
                });
                if gcd == 0 && *rhs == 0 {
                    //dbg!("LinDep");
                    del_idx.push(idx);
                    return false;
                }
                let res = rhs.clone() % &gcd != 0;
                if gcd != 1 {
                    for x in coeff.iter_mut() {
                        *x /= &gcd;
                    }
                    *rhs /= &gcd;
                }
                coeff.iter().enumerate().for_each(|(i, c)| {
                    if *c != 0 && c.clone().abs() < self.sc_val.clone().abs() {
                        self.sc_val = c.clone();
                        self.sc_eqn = idx;
                        self.sc_cff = i;
                    }
                }); /*
                    let (i,c) = coeff.iter().enumerate().min_by(|(_, a), (_, b)| {
                        a.cmp_abs(b)
                    }).unwrap();
                    self.sc_val.assign(c);
                    self.sc_eqn = idx;
                    self.sc_cff = i;*/
                res
            })
            .any(|x| x)
            .not();
        let mut offset = 0;
        for idx in del_idx {
            self.equations.remove(idx - offset);
            offset += 1;
            if self.sc_eqn > idx {
                self.sc_eqn -= 1;
            }
        }
        if self.sc_val < 0 {
            self.equations[self.sc_eqn].invert_coeff();
            self.equations[self.sc_eqn].rhs *= -1;
            self.sc_val *= -1;
        }

        return res;
    }

    fn solve(&mut self, opt: &Opt) {
        let mut num_elim = 0;
        loop {
            if self.equations.len() == 0 {
                println!("SAT");
                return;
            }
            let _s = self.solvable();
            if opt.debug {
                dbg!(&self.equations);
            }
            /*if self.equations.len() == 1 {
                if s {
                    println!("SAT");
                    return;
                } else {
                    println!("UNSAT");
                    return;
                }
            }*/
            //dbg!("Start round");
            //dbg!(self.sc_val, self.sc_eqn, self.sc_cff);
            let mut replacement = ResolveEquation {
                eqn: Equation::with_coeff_count(self.num_vars),
                names: vec![],
            };

            if self.sc_val == Integer::from(1_i32) {
                //dbg!("One handling");
                //dbg!(&self);
                if self.equations.len() == 1 {
                    let eqn = self.equations[self.sc_eqn].clone();
                    for (i, _) in eqn.coeff.iter().enumerate() {
                        //dbg!(*c, "pre");
                        if i == self.sc_cff {
                            continue;
                        }
                        replacement.eqn.coeff[i] = -eqn.coeff[i].clone();
                    }
                    replacement.eqn.rhs = eqn.rhs.clone();
                }
                let eqn = self.equations[self.sc_eqn].clone();
                for (idx, other) in self.equations.iter_mut().enumerate() {
                    if idx == self.sc_eqn {
                        continue;
                    }
                    let mult = other.coeff[self.sc_cff].clone();
                    if mult == Integer::ZERO {
                        continue;
                    }
                    for (i, c) in other.coeff.iter_mut().enumerate() {
                        //dbg!(*c, "pre");
                        if i == self.sc_cff {
                            continue;
                        }
                        *c -= &eqn.coeff[i] * &mult;
                        replacement.eqn.coeff[i].assign(-&eqn.coeff[i]);
                        //dbg!(eqn.coeff[i], mult);
                        //dbg!(*c, "post");
                    }
                    other.coeff[self.sc_cff] = Integer::ZERO;
                    other.rhs -= &mult * &eqn.rhs;
                    replacement.eqn.rhs.assign(&eqn.rhs);
                }
                self.equations.remove(self.sc_eqn);
                //dbg!(&self);
            } else {
                let ak = self.sc_val.clone();
                //dbg!(&ak);
                let m: Integer = ak + 1;
                //dbg!(&m);

                let mut offs = self.equations[self.sc_eqn].clone();
                for off in offs.coeff.iter_mut() {
                    System::mod_p(off, &m);
                }
                System::mod_p(&mut offs.rhs, &m);

                for other in self.equations.iter_mut() {
                    let mult = other.coeff[self.sc_cff].clone();
                    //dbg!(&mult);
                    if mult == Integer::ZERO {
                        continue;
                    }
                    for (i, c) in other.coeff.iter_mut().enumerate() {
                        //dbg!(*c, "pre");
                        if i == self.sc_cff {
                            continue;
                        }
                        let off = &offs.coeff[i];
                        *c += off * &mult;
                        replacement.eqn.coeff[i].assign(off);
                        //dbg!(eqn.coeff[i], m, System::mod_p(eqn.coeff[i], m));
                        //dbg!(*c, "post");
                    }
                    other.coeff[self.sc_cff].assign(&m * &mult);
                    other.coeff[self.sc_cff] *= -1_i32;
                    replacement.eqn.coeff[self.sc_cff].assign(-&m);
                    other.rhs += &offs.rhs * &mult;
                    replacement.eqn.rhs.assign(-&offs.rhs);
                }
                //dbg!(&self);
                num_elim += 1;
            }
            if opt.debug {
                eprintln!("Eliminated {} vars", num_elim);
            }
            let key = self.var_names[self.sc_cff];
            self.var_names[self.sc_cff].iter += 1;
            replacement.names = self.var_names.clone();
            if self.first_replaced.is_none() {
                self.first_replaced = Some(key);
            }
            self.replaced_by.insert(key, replacement);
            //dbg!(&self);
        }
    }

    fn dump_graph(&self) {
        let edges: Vec<(VarName, VarName, Integer)> = self
            .replaced_by
            .iter()
            .flat_map(|(&k, v)| {
                v.names
                    .iter()
                    .zip(v.eqn.coeff.iter())
                    .map(move |(&x, w)| (k, x, w.clone()))
                    .filter(|(_, _, w)| w != &Integer::ZERO)
            })
            .collect();
        let mut output_file = std::fs::File::create("output.dot").unwrap();
        render_graph(&mut output_file, edges).unwrap();
    }

    fn dfs(&self, curr: VarName, visited: &mut HashMap<VarName, Integer>) -> Integer {
        if let Some(val) = visited.get(&curr) {
            return val.clone();
        }
        return match self.replaced_by.get(&curr) {
            Some(children) => {
                let mut result = children.eqn.rhs.clone();
                for (child, cff) in children.names.iter().zip(children.eqn.coeff.iter()) {
                    let val = self.dfs(*child, visited);
                    result += val * cff;
                }
                visited.insert(curr, result.clone());
                result
            }
            None => {
                visited.insert(curr, Integer::ZERO);
                Integer::ZERO
            }
        };
    }

    fn extract_solution(&self) -> HashMap<VarName, Integer> {
        let mut visited: HashMap<VarName, Integer> = HashMap::new();
        let curr = self.first_replaced.unwrap();
        self.dfs(curr, &mut visited);
        let result: HashMap<_, _> = visited
            .iter()
            .filter_map(|(&k, v)| {
                if k.iter == 0 {
                    return Some((k, v.clone()));
                }
                return None;
            })
            .collect();
        return result;
    }

    fn check_solution(&self, result: &HashMap<VarName, Integer>) {
        for eqn in self.orig_equations.iter() {
            let mut res = Integer::ZERO;
            for (i, cff) in eqn.coeff.iter().enumerate() {
                res += cff * result.get(&VarName { name: i, iter: 0 }).unwrap();
            }
            assert_eq!(res, eqn.rhs);
        }
    }
}

impl FromStr for System {
    type Err = ();
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut data = s
            .split_whitespace()
            .map(|x| x.parse::<Integer>().unwrap())
            .peekable();

        let num_eqs = data.next().unwrap().try_into().unwrap();
        let num_vars: usize = data.next().unwrap().try_into().unwrap();

        //dbg!(num_eqs, num_vars);
        let mut equations = vec![Equation::with_coeff_count(num_vars); num_eqs];
        let mut eqn = 0;
        while data.peek().is_some() {
            data.next(); // Skip first of line
            loop {
                let value = data.next().unwrap();
                let index: usize = data.next().unwrap().try_into().unwrap();
                if index != 0 {
                    equations[eqn].coeff[index - 1] = value;
                } else {
                    equations[eqn].rhs = value;
                    eqn += 1;
                    break;
                }
            }
        }
        Ok(System::new(equations, num_eqs, num_vars))
    }
}

fn main() {
    let opt = Opt::from_args();
    let content = std::fs::read_to_string(&opt.input).unwrap();
    let mut eqns = System::from_str(&content).unwrap();

    //dbg!(&eqns);

    if !eqns.solvable() {
        println!("UNSAT");
        return;
    }
    //dbg!(&eqns);

    eqns.solve(&opt);

    //dbg!(&eqns.replaced_by);

    if opt.dump_dot {
        eqns.dump_graph();
    }

    let result = eqns.extract_solution();

    if opt.debug || opt.print {
        //dbg!(&result);
        let mut res_vec: Vec<_> = result.iter().collect();
        res_vec.sort_by_key(|&(k, _)| k.name);
        for (_, x) in res_vec {
            eprint!("{} ", x);
        }
        eprintln!();
    }

    eqns.check_solution(&result);

    //dbg!(&eqns);
}
