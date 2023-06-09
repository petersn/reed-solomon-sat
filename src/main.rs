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

    fn instantiate(&mut self, template: &CnfTemplate, inputs: &[Lit]) -> Vec<Lit> {
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

#[derive(Debug, Serialize, Deserialize)]
struct SSASlotConfig {
    addr1: Vec<Lit>,
    addr2: Vec<Lit>,
}

#[derive(Debug, Serialize, Deserialize)]
struct SSAConfig {
    input_bits: usize,
    slots: Vec<Vec<SSASlotConfig>>,
    output_addresses: Vec<Vec<Lit>>,
}

fn bits_to_index(bit_count: usize) -> usize {
    bit_count.next_power_of_two().trailing_zeros() as usize
}

fn iter_n_choose_k(n: usize, k: usize) -> impl Iterator<Item=Vec<usize>> {
    assert!(k <= n);
    let mut indices: Vec<usize> = (0..k).collect();
    let mut done = false;
    std::iter::from_fn(move || {
        if done {
            return None;
        }
        let result = indices.clone();
        let mut i = k;
        while i > 0 && indices[i - 1] == n - k + i - 1 {
            i -= 1;
        }
        if i == 0 {
            done = true;
        } else {
            indices[i - 1] += 1;
            for j in i..k {
                indices[j] = indices[j - 1] + 1;
            }
        }
        Some(result)
    })
}

fn main() {
    let mux_templates: HashMap::<usize, CnfTemplate> = (2..11usize).map(|input_count| {
        println!("finding mux of {} bits", input_count);
        let address_count = bits_to_index(input_count);
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

    let add_mux = |instance: &mut SatInstance, addr: &[Lit], inputs: &[Lit]| -> Lit {
        assert_eq!(addr.len(), bits_to_index(inputs.len()));
        let cnf = mux_templates.get(&inputs.len()).unwrap();
        let all_inputs: Vec<_> = addr.iter().chain(inputs.iter()).copied().collect();
        match &instance.instantiate(cnf, &all_inputs)[..] {
            [output] => *output,
            _ => unreachable!(),
        }
    };

    fn make_ssa_config(
        instance: &mut SatInstance,
        input_bits: usize,
        output_bits: usize,
    ) -> SSAConfig {
        let mut ssa_values = input_bits;
        let mut slots = Vec::new();
        for _ in 0..cycles {
            let mut row = Vec::new();
            for _ in 0..instructions_per_cycle {
                row.push(SSASlotConfig {
                    addr1: instance.n_fresh(bits_to_index(ssa_values)),
                    addr2: instance.n_fresh(bits_to_index(ssa_values)),
                });
            }
            slots.push(row);
            ssa_values += instructions_per_cycle;
        }
        let output_addresses = (0..output_bits).map(
            |_| instance.n_fresh(bits_to_index(ssa_values))
        ).collect();
        SSAConfig { input_bits, slots, output_addresses }
    }

    let evaluate_ssa = |instance: &mut SatInstance, input_bits: &[Lit], config: &SSAConfig| {
        assert!(input_bits.len() == config.input_bits);
        let mut ssa_values = input_bits.to_vec();
        for cycle in &config.slots {
            let mut cycle_values = Vec::new();
            for slot in cycle {
                let data1 = add_mux(instance, &slot.addr1, &ssa_values);
                let data2 = add_mux(instance, &slot.addr2, &ssa_values);
                cycle_values.push(instance.instantiate(&xor2_template, &[data1, data2])[0]);
            }
            ssa_values.extend(cycle_values);
        }
        let mut outputs = Vec::new();
        for addr in &config.output_addresses {
            outputs.push(add_mux(instance, addr, &ssa_values));
        }
        outputs
    };

    let mut instance = SatInstance::default();
    let true_lit = instance.fresh();
    instance.clauses.push(vec![true_lit]);
    let false_lit = -true_lit;

    const chunks_per_shard: usize = 1;
    const d: usize = 2;
    const p: usize = 1;
    const instructions_per_cycle: usize = 1;
    const cycles: usize = 4;

    let encoder_config = make_ssa_config(
        &mut instance,
        chunks_per_shard * d,
        chunks_per_shard * p,
    );

    // I keep getting myself confused, so let's enforce this with types.
    #[derive(Debug, Clone, Copy)] struct ChunkIndex(usize);
    #[derive(Debug, Clone, Copy)] struct ShardIndex(usize);
    #[derive(Debug)] struct ChunkVec<T>(Vec<T>);
    impl<T> ChunkVec<T> {
        fn from(values: Vec<T>) -> Self {
            assert_eq!(values.len(), chunks_per_shard);
            ChunkVec(values)
        }

        fn at_mut(&mut self, index: ChunkIndex) -> &mut T {
            &mut self.0[index.0]
        }
    }
    #[derive(Debug)] struct ShardVec<T>(Vec<T>);
    impl<T> ShardVec<T> {
        fn from(values: Vec<T>) -> Self {
            // These are the only two cases I do right now:
            assert!(values.len() == d || values.len() == p);
            ShardVec(values)
        }

        fn at_mut(&mut self, index: ShardIndex) -> &mut T {
            &mut self.0[index.0]
        }
    }

    // For each input position, we build an SSA evaluation.
    // The value
    //     ssa_evaluations[input_shard][input_chunk][output_shard][output_chunk]
    // says if a given input chunk ends up incorporated in a given output chunk.
    let mut ssa_evaluations: ShardVec<ChunkVec<ShardVec<ChunkVec<Lit>>>> = ShardVec(Vec::new());
    for input_shard in 0..d {
        let mut a = Vec::new();
        for input_chunk in 0..chunks_per_shard {
            let mut one_hot: Vec<Lit> = vec![false_lit; chunks_per_shard * d];
            one_hot[chunks_per_shard * input_shard + input_chunk] = true_lit;
            let outputs = evaluate_ssa(&mut instance, &one_hot, &encoder_config);
            assert!(outputs.len() == chunks_per_shard * p);
            let mut b = Vec::new();
            for output_shard in 0..p {
                let mut c = Vec::new();
                for output_chunk in 0..chunks_per_shard {
                    c.push(outputs[chunks_per_shard * output_shard + output_chunk]);
                }
                b.push(ChunkVec::from(c));
            }
            a.push(ShardVec::from(b));
        }
        ssa_evaluations.0.push(ChunkVec::from(a));
    }

    // (0..chunks_per_shard * d).map(|data_pattern| {
    //     let mut one_hot: Vec<Lit> = vec![false_lit; chunks_per_shard * d];
    //     one_hot[data_pattern] = true_lit;
    //     evaluate_ssa(&mut instance, &one_hot, &encoder_config)
    // }).collect();
    println!("SSA evaluations: {:?}", ssa_evaluations);

    // We now need to iterate over all possible recovery scenarios.
    for shards_we_have in iter_n_choose_k(d + p, d) {
        // Skip the trivial recovery.
        if *shards_we_have.iter().max().unwrap() == d - 1 {
            continue;
        }
        let shards_we_have: Vec<ShardIndex> = shards_we_have.iter().copied().map(ShardIndex).collect();
        println!("-- Adding clauses for recovering from {:?}", shards_we_have);
        let decoder_config = make_ssa_config(
            &mut instance, chunks_per_shard * d, chunks_per_shard * d,
        );

        // We test chunkwise.
        for input_chunk in (0..chunks_per_shard).map(ChunkIndex) {
            // We now specify for each chunk we got, whether or not it contains this input chunk.
            let mut input_bits: Vec<Lit> = Vec::new();
            for have_shard_index in &shards_we_have {
                for have_chunk in (0..chunks_per_shard).map(ChunkIndex) {
                    // Check if this is a data shard, or a parity shard.
                    let new_bit = if have_shard_index.0 < d {
                        if have_shard_index.0 == input_shard && have_chunk == input_chunk {
                            true_lit
                        } else {
                            false_lit
                        }
                    } else {
                    }
                    input_bits.push(new_bit);
                }
            }
            // Make sure we recovered each output appropriately.
            for recovered_shard in 0..d {
                
            }
        }
    }
}
