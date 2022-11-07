// This file is adapted from Webb and Arkworks:
// https://github.com/webb-tools/arkworks-gadgets

// Copyright (C) 2021 Webb Technologies Inc.
// SPDX-License-Identifier: Apache-2.0

// Copyright (c) zkMove Authors
// SPDX-License-Identifier: Apache-2.0

//! A Plonk gadget implementation of the Sparse Merkle Tree data structure.
//! For more info on the Sparse Merkle Tree data structure, see the
//! documentation for the native implementation.


use crate::poseidon_chip::{PoseidonChip, PoseidonConfig};
use crate::utilities::{
    AssertEqualChip, AssertEqualConfig, ConditionalSelectChip, ConditionalSelectConfig,
    IsEqualChip, IsEqualConfig, NUM_OF_UTILITY_ADVICE_COLUMNS,
};
use halo2_gadgets::poseidon::primitives::Spec;
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{AssignedCell, Layouter, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Selector},
};
use smt::poseidon::FieldHasher;
use smt::smt::Path;
use std::marker::PhantomData;

#[derive(Clone)]
pub struct PathConfig<
    F: FieldExt,
    S: Spec<F, WIDTH, RATE>,
    const WIDTH: usize,
    const RATE: usize,
    const N: usize,
> {
    s_path: Selector,
    advices: [Column<Advice>; N],
    poseidon_config: PoseidonConfig<F, WIDTH, RATE>,
    is_eq_config: IsEqualConfig<F>,
    conditional_select_config: ConditionalSelectConfig<F>,
    assert_equal_config: AssertEqualConfig<F>,
    _spec: PhantomData<S>,
}

pub struct PathChip<
    F: FieldExt,
    S: Spec<F, WIDTH, RATE>,
    H: FieldHasher<F, 2>,
    const WIDTH: usize,
    const RATE: usize,
    const N: usize,
> {
    path: [(AssignedCell<F, F>, AssignedCell<F, F>); N],
    poseidon_chip: PoseidonChip<F, S, WIDTH, RATE, 2>,
    is_eq_chip: IsEqualChip<F>,
    conditional_select_chip: ConditionalSelectChip<F>,
    assert_equal_chip: AssertEqualChip<F>,
    _spec: PhantomData<S>,
    _hasher: PhantomData<H>,
}

impl<
        F: FieldExt,
        S: Spec<F, WIDTH, RATE>,
        H: FieldHasher<F, 2>,
        const WIDTH: usize,
        const RATE: usize,
        const N: usize,
    > PathChip<F, S, H, WIDTH, RATE, N>
{
    pub fn configure(meta: &mut ConstraintSystem<F>) -> PathConfig<F, S, WIDTH, RATE, N> {
        let s_path = meta.selector();
        let advices = [(); N].map(|_| meta.advice_column());
        let utility_advices = [(); NUM_OF_UTILITY_ADVICE_COLUMNS].map(|_| meta.advice_column());

        advices
            .iter()
            .for_each(|column| meta.enable_equality(*column));
        utility_advices
            .iter()
            .for_each(|column| meta.enable_equality(*column));

        PathConfig {
            s_path,
            advices,
            poseidon_config: PoseidonChip::<F, S, WIDTH, RATE, 2>::configure(meta),
            is_eq_config: IsEqualChip::configure(meta, utility_advices),
            conditional_select_config: ConditionalSelectChip::configure(meta, utility_advices),
            assert_equal_config: AssertEqualChip::configure(
                meta,
                [utility_advices[0], utility_advices[1]],
            ),
            _spec: PhantomData,
        }
    }

    pub fn from_native(
        config: PathConfig<F, S, WIDTH, RATE, N>,
        layouter: &mut impl Layouter<F>,
        native: Path<F, H, N>,
    ) -> Result<Self, Error> {
        let path = layouter.assign_region(
            || "path",
            |mut region| {
                config.s_path.enable(&mut region, 0)?;
                let left = (0..N)
                    .map(|i| {
                        region.assign_advice(
                            || format!("path[{}][{}]", i, 0),
                            config.advices[i],
                            0,
                            || Value::known(native.path[i].0),
                        )
                    })
                    .collect::<Result<Vec<AssignedCell<F, F>>, Error>>();

                let right = (0..N)
                    .map(|i| {
                        region.assign_advice(
                            || format!("path[{}][{}]", i, 1),
                            config.advices[i],
                            1,
                            || Value::known(native.path[i].1),
                        )
                    })
                    .collect::<Result<Vec<AssignedCell<F, F>>, Error>>();

                let result = left?
                    .into_iter()
                    .zip(right?.into_iter())
                    .collect::<Vec<(AssignedCell<F, F>, AssignedCell<F, F>)>>();
                Ok(result.try_into().unwrap())
            },
        )?;

        Ok(PathChip {
            path,
            poseidon_chip: PoseidonChip::<F, S, WIDTH, RATE, 2>::construct(config.poseidon_config),
            is_eq_chip: IsEqualChip::construct(config.is_eq_config, ()),
            conditional_select_chip: ConditionalSelectChip::construct(
                config.conditional_select_config,
                (),
            ),
            assert_equal_chip: AssertEqualChip::construct(config.assert_equal_config, ()),
            _spec: PhantomData,
            _hasher: PhantomData,
        })
    }

    pub fn calculate_root(
        &self,
        layouter: &mut impl Layouter<F>,
        leaf: AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        // Check levels between leaf level and root
        let mut previous_hash = leaf;

        for (left_hash, right_hash) in self.path.iter() {
            // Check if previous_hash matches the correct current hash
            let previous_is_left = self.is_eq_chip.is_eq_with_output(
                layouter,
                previous_hash.clone(),
                left_hash.clone(),
            )?;
            let left_or_right = self.conditional_select_chip.conditional_select(
                layouter,
                left_hash.clone(),
                right_hash.clone(),
                previous_is_left,
            )?;
            self.assert_equal_chip
                .assert_equal(layouter, previous_hash, left_or_right)?;

            // Update previous_hash
            previous_hash = self
                .poseidon_chip
                .hash(layouter, &[left_hash.clone(), right_hash.clone()])?;
        }

        Ok(previous_hash)
    }

    pub fn check_membership(
        &self,
        layouter: &mut impl Layouter<F>,
        root_hash: AssignedCell<F, F>,
        leaf: AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        let computed_root = self.calculate_root(layouter, leaf)?;

        self.is_eq_chip
            .is_eq_with_output(layouter, computed_root, root_hash)
    }
}


#[cfg(test)]
mod test {

    use super::{PathChip, PathConfig};
    use crate::utilities::{AssertEqualChip, AssertEqualConfig};
    use crate::measure;
    use halo2_gadgets::poseidon::primitives::Spec;
    use halo2_proofs::plonk::{create_proof, keygen_pk, keygen_vk, verify_proof, SingleVerifier};
    use halo2_proofs::poly::commitment::Params;
    use halo2_proofs::transcript::{Blake2bRead, Blake2bWrite, Challenge255};
    use halo2_proofs::{
        arithmetic::{Field, FieldExt},
        circuit::{Layouter, SimpleFloorPlanner, Value},
        plonk::{Advice, Circuit, Column, ConstraintSystem, Error},
    };
    use halo2_proofs::{dev::MockProver, pasta::EqAffine, pasta::Fp};
    use rand::rngs::OsRng;
    use smt::poseidon::{FieldHasher, Poseidon, SmtP128Pow5T3};
    use smt::smt::SparseMerkleTree;
    use std::clone::Clone;
    use std::marker::PhantomData;
    use std::time::Instant;

    #[derive(Clone)]
    struct TestConfig<
        F: FieldExt,
        S: Spec<F, WIDTH, RATE>,
        H: FieldHasher<F, 2>,
        const WIDTH: usize,
        const RATE: usize,
        const N: usize,
    > {
        path_config: PathConfig<F, S, WIDTH, RATE, N>,
        advices: [Column<Advice>; 3],
        assert_equal_config: AssertEqualConfig<F>,
        _hasher: PhantomData<H>,
    }

    struct TestCircuit<
        F: FieldExt,
        S: Spec<F, WIDTH, RATE>,
        H: FieldHasher<F, 2>,
        const WIDTH: usize,
        const RATE: usize,
        const N: usize,
    > {
        leaves: [F; 3],
        empty_leaf: [u8; 64],
        hasher: H,
        _spec: PhantomData<S>,
    }

    impl<
            F: FieldExt,
            S: Spec<F, WIDTH, RATE> + Clone,
            H: FieldHasher<F, 2> + Clone,
            const WIDTH: usize,
            const RATE: usize,
            const N: usize,
        > Circuit<F> for TestCircuit<F, S, H, WIDTH, RATE, N>
    {
        type Config = TestConfig<F, S, H, WIDTH, RATE, N>;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self {
                leaves: [F::zero(), F::zero(), F::zero()],
                empty_leaf: [0u8; 64],
                hasher: H::hasher(),
                _spec: PhantomData,
            }
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let advices = [(); 3].map(|_| meta.advice_column());
            advices
                .iter()
                .for_each(|column| meta.enable_equality(*column));

            TestConfig {
                path_config: PathChip::<F, S, H, WIDTH, RATE, N>::configure(meta),
                advices,
                assert_equal_config: AssertEqualChip::configure(meta, [advices[0], advices[1]]),
                _hasher: PhantomData,
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let smt = SparseMerkleTree::<F, H, N>::new_sequential(
                &self.leaves,
                &self.hasher.clone(),
                &self.empty_leaf,
            )
            .unwrap();
            let path = smt.generate_membership_proof(0);
            let root = path
                .calculate_root(&self.leaves[0], &self.hasher.clone())
                .unwrap();

            let (root_cell, leaf_cell, one) = layouter.assign_region(
                || "test circuit",
                |mut region| {
                    let root_cell = region.assign_advice(
                        || "root",
                        config.advices[0],
                        0,
                        || Value::known(root),
                    )?;

                    let leaf_cell = region.assign_advice(
                        || "leaf",
                        config.advices[1],
                        0,
                        || Value::known(self.leaves[0]),
                    )?;

                    let one = region.assign_advice(
                        || "one",
                        config.advices[2],
                        0,
                        || Value::known(F::one()),
                    )?;
                    Ok((root_cell, leaf_cell, one))
                },
            )?;

            let path_chip = PathChip::<F, S, H, WIDTH, RATE, N>::from_native(
                config.path_config,
                &mut layouter,
                path,
            )?;
            let res = path_chip.check_membership(&mut layouter, root_cell, leaf_cell)?;

            let assert_equal_chip = AssertEqualChip::construct(config.assert_equal_config, ());
            assert_equal_chip.assert_equal(&mut layouter, res, one)?;

            Ok(())
        }
    }

    #[test]
    fn should_verify_path() {
        // Circuit is very small, we pick a small value here
        let k = 13;

        let empty_leaf = [0u8; 64];
        let rng = OsRng;
        let leaves = [Fp::random(rng), Fp::random(rng), Fp::random(rng)];
        const HEIGHT: usize = 3;

        let circuit = TestCircuit::<Fp, SmtP128Pow5T3<Fp, 0>, Poseidon<Fp, 2>, 3, 2, HEIGHT> {
            leaves,
            empty_leaf,
            hasher: Poseidon::<Fp, 2>::new(),
            _spec: PhantomData,
        };

        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));

        let now = Instant::now();
        let params: Params<EqAffine> = Params::new(k);
        let vk = keygen_vk(&params, &circuit).expect("keygen_vk should not fail");
        let pk = keygen_pk(&params, vk, &circuit).expect("keygen_pk should not fail");
        println!("keygen time is {:?}", now.elapsed());

        let now = Instant::now();
        let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
        create_proof(&params, &pk, &[circuit], &[&[]], OsRng, &mut transcript)
            .expect("proof generation should not fail");
        let proof: Vec<u8> = transcript.finalize();
        println!("create_proof time is {:?}", now.elapsed());

        let now = Instant::now();
        let strategy = SingleVerifier::new(&params);
        let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
        let result = verify_proof(&params, pk.get_vk(), strategy, &[&[]], &mut transcript);
        println!("verify_proof time is {:?}", now.elapsed());

        assert!(result.is_ok());
    }

    #[test]
    #[allow(path_statements)]
    fn should_verify_path_benchmark() {
        // Circuit is very small, we pick a small value here
        let k = 13;

        let empty_leaf = [0u8; 64];
        let rng = OsRng;
        let leaves = [Fp::random(rng), Fp::random(rng), Fp::random(rng)];
        const HEIGHT: usize = 3;
        let num_iter =3;

        measure!({
            let circuit = TestCircuit::<Fp, SmtP128Pow5T3<Fp, 0>, Poseidon<Fp, 2>, 3, 2, HEIGHT> {
                leaves,
                empty_leaf,
                hasher: Poseidon::<Fp, 2>::new(),
                _spec: PhantomData,
            };

            let prover = MockProver::run(k, &circuit, vec![]).unwrap();
            assert_eq!(prover.verify(), Ok(()));

            let params: Params<EqAffine> = Params::new(k);
            let vk = keygen_vk(&params, &circuit).expect("keygen_vk should not fail");
            let pk = keygen_pk(&params, vk, &circuit).expect("keygen_pk should not fail");
            let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
            create_proof(&params, &pk, &[circuit], &[&[]], OsRng, &mut transcript)
                .expect("proof generation should not fail");
            let proof: Vec<u8> = transcript.finalize();

            let strategy = SingleVerifier::new(&params);
            let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
            let result = verify_proof(&params, pk.get_vk(), strategy, &[&[]], &mut transcript);
            assert!(result.is_ok());
        }, "hola2", "proof", num_iter);
    }
}
