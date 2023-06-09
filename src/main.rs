use std::collections::HashMap;

use serde::{Serialize, Deserialize};
use autosat::{SatOutput, SatLiteral as Lit};

static CACHE_PATH: &str = "cnf_cache.json";

#[derive(Clone, Default, Serialize, Deserialize)]
struct CnfTemplate {
    num_inputs: usize,
    num_outputs: usize,
    cnf: Vec<Vec<Lit>>,
}

#[derive(Default, Serialize, Deserialize)]
struct CnfCache {
    entries: HashMap<String, CnfTemplate>,
}

fn convert_to_cnf_cached(
    num_inputs: usize,
    num_outputs: usize,
    f: impl Fn(&[bool]) -> SatOutput,
) -> CnfTemplate {
    let bit_count = num_inputs + num_outputs;

    // Construct a short key that uniquely identifies the function.
    let mut key_string = format!("{}:{}:", num_inputs, num_outputs);
    for i in 0..(1 << bit_count) {
        let bits: Vec<bool> = (0..bit_count).map(|j| (i >> j) & 1 == 1).collect();
        match f(&bits) {
            SatOutput::Bits(result) => {
                for bit in result {
                    key_string.push(if bit { '1' } else { '0' });
                }
            }
            SatOutput::ImpossibleInputs => key_string.push('I'),
            SatOutput::DontCare => key_string.push('D'),
        }
    }
    let key = sha256::digest(key_string.as_bytes());

    // Check the cache.
    let mut cache: CnfCache = match std::fs::read_to_string(CACHE_PATH) {
        Ok(contents) => serde_json::from_str(&contents).unwrap(),
        Err(_) => Default::default(),
    };
    match cache.entries.get_mut(&key) {
        Some(mut entry) => std::mem::take(&mut entry),
        None => {
            let cnf = autosat::convert_to_cnf(num_inputs, num_outputs, f);
            let template = CnfTemplate { num_inputs, num_outputs, cnf };
            cache.entries.insert(key, template.clone());
            let mut serialized = serde_json::to_string(&cache).unwrap();
            serialized.push('\n');
            std::fs::write(CACHE_PATH, serialized).unwrap();
            template
        }
    }
}

#[derive(Default, Debug)]
struct SatInstance {
    clauses:     Vec<Vec<Lit>>,
    var_counter: Lit,
}

impl SatInstance {
    fn fresh(&mut self) -> Lit {
        self.var_counter += 1;
        self.var_counter
    }
    
    fn n_fresh(&mut self, n: usize) -> Vec<Lit> {
        (0..n).map(|_| self.fresh()).collect()
    }

    fn instantiate(&mut self, inputs: &[Lit], template: &CnfTemplate) -> Vec<Lit> {
        assert!(inputs.len() == template.num_inputs);
        let outputs = self.n_fresh(template.num_outputs);
        for template_clause in &template.cnf {
            let mut clause = template_clause.clone();
            for lit in &mut clause {
                let i = lit.abs() as usize;
                assert!(0 < i && i <= template.num_inputs + template.num_outputs);
                let real_var = match i <= template.num_inputs {
                    true => inputs[i - 1],
                    false => outputs[i - 1 - template.num_inputs],
                };
                *lit = if lit.is_positive() { real_var } else { -real_var };
            }
            self.clauses.push(clause);
        }
        outputs
    }
}

fn main() {
    let mux_templates: HashMap::<usize, CnfTemplate> = (2..11usize).map(|input_count| {
        println!("finding mux of {} bits", input_count);
        let address_count = input_count.next_power_of_two().trailing_zeros() as usize;
        let template = convert_to_cnf_cached(address_count + input_count, 1, |inp| {
            let mut address = 0;
            for (i, b) in inp[0..address_count].iter().enumerate() {
                address |= (*b as usize) << i;
            }
            if address >= input_count {
                return autosat::SatOutput::ImpossibleInputs;
            }
            let indexed = inp[address_count + address];
            return autosat::SatOutput::Bits(vec![indexed]);
        });
        (input_count, template)
    }).collect();
    let xor2_template = convert_to_cnf_cached(2, 1, |inp| {
        autosat::SatOutput::Bits(vec![inp[0] ^ inp[1]])
    });
    let xor3_template = convert_to_cnf_cached(3, 1, |inp| {
        autosat::SatOutput::Bits(vec![inp[0] ^ inp[1] ^ inp[2]])
    });

    let add_mux = |instance: &mut SatInstance, addr: &[Lit], inputs: &[Lit]| -> Lit {
        assert_eq!(addr.len(), inputs.len().next_power_of_two().trailing_zeros() as usize);
        let cnf = mux_templates.get(&inputs.len()).unwrap();
        let all_inputs: Vec<_> = addr.iter().chain(inputs.iter()).copied().collect();
        match &instance.instantiate(&all_inputs, cnf)[..] {
            [output] => *output,
            _ => unreachable!(),
        }
    };

    //let make_ssa_config = |instance: &mut SatInstance, 

    let mut instance = SatInstance::default();
    let addr = instance.n_fresh(2);
    let data = instance.n_fresh(4);
    let muxed = add_mux(&mut instance, &addr, &data);
    println!("Instance: {:?} -> {:?}", instance, muxed);
}
