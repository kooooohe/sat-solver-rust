use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::VecDeque;
use std::fs::File;
use std::io::BufRead;
use std::result::Result;
use std::vec;

#[derive(Clone, PartialEq, Debug)]
enum VarState {
    True,
    False,
    None,
}

#[derive(Debug)]
struct Node {
    variable: usize,
    value: bool,
    decision_level: usize,
    antecedent: Option<Clause>,
}

#[derive(Clone, Debug)]
struct Clause {
    literals: Vec<Literal>,
    watch_index: [usize; 2],
}

enum TwoWatchResult {
    Conflict,
    UnitPropagation(usize),
    Satisfied,
    Unresolved,
}

impl Clause {
    fn new() -> Self {
        Clause {
            literals: vec![],
            watch_index: [0, 1],
        }
    }
    fn watch_two_literal(&mut self, x: &[VarState]) -> TwoWatchResult {
        if self.literals.len() == 1 {
            match &x[self.literals[0].variable] {
                VarState::None => {
                    return TwoWatchResult::UnitPropagation(self.literals[0].variable)
                }
                t => {
                    let v = if self.literals[0].nagated {
                        VarState::False
                    } else {
                        VarState::True
                    };

                    if *t == v {
                        return TwoWatchResult::Satisfied;
                    } else {
                        return TwoWatchResult::Conflict;
                    }
                }
            }
        }
        let watch1_lit = &self.literals[self.watch_index[0]];
        let watch2_lit = &self.literals[self.watch_index[1]];

        let watch1_sat = watch1_lit.is_satisfied(&x[watch1_lit.variable]);
        let watch2_sat = watch2_lit.is_satisfied(&x[watch2_lit.variable]);

        match (watch1_sat, watch2_sat) {
            (None, None) => return TwoWatchResult::Unresolved,
            (Some(true), _) | (_, Some(true)) => return TwoWatchResult::Satisfied,
            _ => (),
        };

        let mut j = 0;
        if x[watch1_lit.variable] != VarState::None {
            for i in 0..self.literals.len() {
                if i == self.watch_index[1] {
                    continue;
                }

                if self.literals[i].is_satisfied(&x[self.literals[i].variable]) == Some(true) {
                    return TwoWatchResult::Satisfied;
                }

                if x[self.literals[i].variable] == VarState::None {
                    self.watch_index[0] = i;
                    j = i;
                    break;
                }
            }
        }

        if x[watch2_lit.variable] != VarState::None {
            for i in j..self.literals.len() {
                if i == self.watch_index[0] {
                    continue;
                }
                if self.literals[i].is_satisfied(&x[self.literals[i].variable]) == Some(true) {
                    return TwoWatchResult::Satisfied;
                }

                if x[self.literals[i].variable] == VarState::None {
                    self.watch_index[1] = i;
                    break;
                }
            }
        }

        let watch1_lit = &self.literals[self.watch_index[0]];
        let watch2_lit = &self.literals[self.watch_index[1]];

        let watch1_sat = watch1_lit.is_satisfied(&x[watch1_lit.variable]);
        let watch2_sat = watch2_lit.is_satisfied(&x[watch2_lit.variable]);

        match (watch1_sat, watch2_sat) {
            (None, None) => TwoWatchResult::Unresolved,
            (Some(true), _) | (_, Some(true)) => TwoWatchResult::Satisfied,
            (Some(false), None) => TwoWatchResult::UnitPropagation(watch2_lit.variable),
            (None, Some(false)) => TwoWatchResult::UnitPropagation(watch1_lit.variable),
            (Some(false), Some(false)) => TwoWatchResult::Conflict,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
struct Literal {
    variable: usize,
    nagated: bool,
}

impl Literal {
    fn is_satisfied(&self, vs: &VarState) -> Option<bool> {
        if *vs == VarState::None {
            return None;
        }
        if self.nagated {
            return Some(*vs == VarState::False);
        } else {
            return Some(*vs == VarState::True);
        }
    }
}

#[derive(Debug)]
struct ImplicationGraph {
    nodes: HashMap<usize, Node>,
    desitions: Vec<usize>,
}

impl ImplicationGraph {
    fn new() -> Self {
        ImplicationGraph {
            nodes: HashMap::new(),
            desitions: vec![],
        }
    }

    fn add_node(
        &mut self,
        variable: usize,
        value: bool,
        decision_level: usize,
        antecedent: Option<Clause>,
    ) {
        self.nodes.insert(
            variable,
            Node {
                variable,
                value,
                decision_level,
                antecedent,
            },
        );
        if decision_level == self.desitions.len() {
            self.desitions.push(variable);
        }
    }

    fn node(&self, variable: usize) -> Option<&Node> {
        self.nodes.get(&variable)
    }

    fn backtrack(&mut self, decision_level: usize, x: &mut Vec<VarState>) {
        let mut to_remove = vec![];
        for (variable, node) in &self.nodes {
            if node.decision_level >= decision_level {
                to_remove.push(*variable);
                x[*variable] = VarState::None;
            }
        }
        for variable in to_remove {
            self.nodes.remove(&variable);
        }
        self.desitions.truncate(decision_level);
    }
    fn analyze(
        &self,
        conflict_clause: Clause,
        dl: usize,
    ) -> Result<(Clause, usize), std::io::Error> {
        let mut seen: HashSet<usize> = HashSet::new();
        // for BFS
        let mut que: VecDeque<Literal> = VecDeque::new();
        let backtrack_level: usize;

        for literal in &conflict_clause.literals {
            que.push_front(literal.clone());
        }

        loop {
            // to check the nodes levels, if it contains one literal in the current literal, finish

            if que.len() == 1 {
                backtrack_level = 0;
                break;
            }

            {
                let mut i = 0;
                let mut second_highest = 0;
                for lit_v in &que {
                    if let Some(node) = self.node(lit_v.variable) {
                        // if node.decision_level == self.desitions.len() {
                        if node.decision_level == dl {
                            i += 1;
                            if i > 1 {
                                break;
                            }
                        } else {
                            if node.decision_level > second_highest {
                                second_highest = node.decision_level;
                            }
                        }
                    }
                }
                // check if it contains only one literal in the current decision level
                if i == 1 {
                    backtrack_level = second_highest;
                    break;
                }
            }
            if let Some(literal) = que.pop_back() {
                if let Some(node) = self.node(literal.variable) {
                    if seen.contains(&literal.variable) {
                        continue;
                    }
                    seen.insert(literal.variable);

                    if let Some(antecedent) = &node.antecedent {
                        for ante_lit in &antecedent.literals {
                            if !seen.contains(&ante_lit.variable) && !que.contains(&ante_lit) {
                                que.push_front(ante_lit.clone());
                            }
                        }
                    }
                } else {
                    return Err(std::io::Error::new(
                        std::io::ErrorKind::InvalidData,
                        "node not found",
                    ));
                }
            } else {
                return Err(std::io::Error::new(
                    std::io::ErrorKind::InvalidData,
                    "queue is empty",
                ));
            }
        }

        let mut learned_clause = Clause::new();
        for lit_v in &que {
            if let Some(node) = self.node(lit_v.variable) {
                learned_clause.literals.push(Literal {
                    variable: lit_v.variable,
                    nagated: node.value,
                });
            }
        }

        Ok((learned_clause, backtrack_level))
    }
}


enum Conflict {
    Yes(Clause),
    No,
}

fn unit_propagete(
    x: &mut Vec<VarState>,
    cnf: &mut Vec<Clause>,
    decision_level: usize,
    i_graph: &mut ImplicationGraph,
) -> Conflict {
    let mut done = false;
    while !done {
        done = true;
        for clause in &mut *cnf {
            let ii = match clause.watch_two_literal(x) {
                TwoWatchResult::Conflict => {
                    return Conflict::Yes(clause.clone());
                }
                TwoWatchResult::UnitPropagation(i) => i,
                TwoWatchResult::Satisfied => continue,
                TwoWatchResult::Unresolved => continue,
            };

            let t_lit = match clause.literals.iter().find(|x| x.variable == ii) {
                Some(t) => t,
                //TODO
                None => return Conflict::No,
            };

            if t_lit.nagated {
                x[ii] = VarState::False;
            } else {
                x[ii] = VarState::True;
            }

            i_graph.add_node(
                ii,
                x[ii] == VarState::False,
                decision_level,
                Some(clause.clone()),
            );
            done = false;

        }
    }
    Conflict::No
}

fn solve(x: &mut Vec<VarState>, cnf: &mut Vec<Clause>) -> Option<bool> {
    let mut desicion_level = 0_usize;
    let mut i_grapgh = ImplicationGraph::new();
    loop {
        if let Conflict::Yes(conflict_clause) =
            unit_propagete(x, cnf, desicion_level, &mut i_grapgh)
        {
            if desicion_level == 0 {
                return Some(false);
            }
            let (learned_clause, backtrack_level) =
                match i_grapgh.analyze(conflict_clause, desicion_level) {
                    Ok((learned_clause, backtrack_level)) => (learned_clause, backtrack_level),
                    Err(_) => {
                        println!("error");
                        return None;
                    }
                };
            cnf.push(learned_clause);
            i_grapgh.backtrack(backtrack_level, x);
            if backtrack_level == 0 {
                desicion_level = 0
            } else {
                desicion_level = backtrack_level - 1;
            }
        } else {
            let i = match x.iter().position(|x| *x == VarState::None) {
                Some(i) => i,
                None => return Some(true),
            };
            desicion_level += 1;
            x[i] = VarState::False;
            i_grapgh.add_node(i, true, desicion_level, None);
        }
    }
}

fn read_file(path: &str) -> Result<(Vec<Clause>, usize), std::io::Error> {
    use std::io::BufReader;
    let f = File::open(&path)?;
    let reader = BufReader::new(f);
    let mut cnf: Vec<Clause> = Vec::new();
    let mut n_v: usize = 0;
    for (i, line) in reader.lines().enumerate() {
        if i == 0 {
            n_v = line?.split_whitespace().nth(2).unwrap().parse().unwrap();
            continue;
        }
        let row: Vec<i32> = line?
            .split_whitespace()
            .filter(|x| *x != "0")
            .map(|x: &str| -> i32 { x.parse().unwrap() })
            .collect();
        let mut c = Clause::new();
        for x in row {
            if x > 0 {
                c.literals.push(Literal {
                    variable: (x - 1) as usize,
                    nagated: false,
                });
            } else {
                c.literals.push(Literal {
                    variable: (-x - 1) as usize,
                    nagated: true,
                });
            }
        }

        if c.literals.len() == 1 {
            c.watch_index[1] = 0;
        }
        cnf.push(c);
    }

    Ok((cnf, n_v))
}

fn main() -> Result<(), std::io::Error> {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 2 {
        eprintln!("Usage: {} <cnf file>", args[0]);
        std::process::exit(2);
    }

    let path = &args[1];
    let f_i = read_file(path)?;
    let mut cnf = f_i.0;
    let mut x = vec![VarState::None; f_i.1];

    match solve(&mut x, &mut cnf) {
        Some(r) => {
            if r {
                println!("s SATISFIABLE");
                print!("v ");
            } else {
                println!("s UNSATISFIABLE");
                return Ok(());
            }
        }
        None => {
            println!("s UNSATISFIABLE");
            return Ok(());
        }
    };

    for i in 0..x.len() {
        if x[i] == VarState::True {
            print!("{} ", i + 1);
        } else {
            print!("-{} ", i + 1);
        }
    }
    print!("{}", 0);

    Ok(())
}
