use std::marker::PhantomData;

use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner},
    dev::MockProver,
    plonk::{self, Circuit, ConstraintSystem},
};

use halo2_proofs::poly::Rotation;
use halo2_proofs::plonk::Selector;
use halo2_proofs::plonk::Advice;
use halo2_proofs::plonk::Column;
use halo2_proofs::plonk::Expression;
use halo2_proofs::circuit::Value;

use halo2_proofs::plonk::Error;
use ff::Field;



struct TestCircuit<F: Field> {
    _ph: PhantomData<F>,
    values: Option<Vec<F>>,
}

const STEPS: usize = 6;

#[derive(Clone, Debug)]
struct TestConfig<F: Field + Clone> {
    _ph: PhantomData<F>,
    q_enable: Selector,
    advice: Column<Advice>,
}

impl<F: Field> Circuit<F> for TestCircuit<F> {
    type Config = TestConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        TestCircuit { 
            _ph: PhantomData,
            values: None,
        }
    }

    #[allow(unused_variables)]
    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let q_enable = meta.complex_selector();
        let advice = meta.advice_column();

        //define a new gate:
        // next = curr + 1 if q_enable is 1
        meta.create_gate("step", |meta| {
            let curr = meta.query_advice(advice, Rotation::cur());
            let prev = meta.query_advice(advice, Rotation::prev());
            let next = meta.query_advice(advice, Rotation::next());
            let q_enable = meta.query_selector(q_enable);
            vec![q_enable * (next - (curr + prev))]
        });

        TestConfig {
            advice,
            q_enable,
            _ph: PhantomData,
        }
    }

    #[allow(unused_variables)]
    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "steps",
            |mut region| {

                region.assign_advice(
                    || "assign advice",
                    config.advice,
                    0,
                    || Value::known(self.values.as_ref().unwrap()[0]),
                )?;
    
                region.assign_advice(
                    || "assign advice",
                    config.advice,
                    1,
                    || Value::known(self.values.as_ref().unwrap()[1]),
                )?;

                for i in 2..STEPS-1 {
                    region.assign_advice(
                        || "assign advice",
                        config.advice,
                        i,
                        || {self.values
                                .as_ref()
                                .map(|values| Value::known(values[i]))
                                .unwrap_or(Value::unknown())},
                    )?;

                    config.q_enable.enable(&mut region, i)?;
                }

               
                region.assign_advice(
                    || "assign advice",
                    config.advice,
                    STEPS - 1,
                    || {self.values
                            .as_ref()
                            .map(|values| Value::known(values[STEPS - 1]))
                            .unwrap_or(Value::unknown())},
                )?;
                
                Ok(())
            },
        )?;
        Ok(())
    }
}

fn main() {
    use halo2_proofs::halo2curves::bn256::Fr;

    let values = Some(vec![
        Fr::from(1u64),
        Fr::from(1u64),
        Fr::from(2u64),
        Fr::from(3u64),
        Fr::from(5u64),
        Fr::from(8u64),
    ]);
    
    let circuit = TestCircuit::<Fr> { _ph: PhantomData, values, };
    let prover = MockProver::run(6, &circuit, vec![]).unwrap();
    match prover.verify() {
        Ok(_) => println!("Proof verified successfully!"),
        Err(err) => println!("Proof verification failed: {:?}", err),
    }
}