// Copyright (c) zkMove Authors
// SPDX-License-Identifier: Apache-2.0

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{AssignedCell, Chip, Layouter, Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Selector},
    poly::Rotation,
};
use std::marker::PhantomData;

const NUM_OF_ADVICE_COLUMNS: usize = 4;

#[derive(Clone, Debug)]
pub struct ConditionalSelectConfig {
    advices: [Column<Advice>; NUM_OF_ADVICE_COLUMNS],
    s_cs: Selector,
}

pub struct ConditionalSelectChip<F: FieldExt> {
    config: ConditionalSelectConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> Chip<F> for ConditionalSelectChip<F> {
    type Config = ConditionalSelectConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F: FieldExt> ConditionalSelectChip<F> {
    pub fn construct(
        config: <Self as Chip<F>>::Config,
        _loaded: <Self as Chip<F>>::Loaded,
    ) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        advices: [Column<Advice>; NUM_OF_ADVICE_COLUMNS],
    ) -> <Self as Chip<F>>::Config {
        for column in &advices {
            meta.enable_equality(*column);
        }
        let s_cs = meta.selector();

        meta.create_gate("conditional_select", |meta| {
            let lhs = meta.query_advice(advices[0], Rotation::cur());
            let rhs = meta.query_advice(advices[1], Rotation::cur());
            let out = meta.query_advice(advices[2], Rotation::cur());
            let cond = meta.query_advice(advices[3], Rotation::cur());
            let s_cs = meta.query_selector(s_cs);

            vec![
                // lhs * cond + rhs * (1 - cond) = out
                s_cs * ((lhs - rhs.clone()) * cond + rhs - out),
            ]
        });

        ConditionalSelectConfig { advices, s_cs }
    }

    pub fn conditional_select(
        &self,
        mut layouter: impl Layouter<F>,
        a: AssignedCell<F, F>,
        b: AssignedCell<F, F>,
        cond: AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        let config = self.config();
        let out = layouter.assign_region(
            || "conditional_select",
            |mut region: Region<'_, F>| {
                config.s_cs.enable(&mut region, 0)?;

                a.copy_advice(|| "copy a", &mut region, config.advices[0], 0)?;

                b.copy_advice(|| "copy b", &mut region, config.advices[1], 0)?;

                let cond = cond.copy_advice(|| "copy cond", &mut region, config.advices[3], 0)?;

                let v = if cond.value().copied() == Value::known(F::one()) {
                    a.value()
                } else {
                    b.value()
                };

                let c = region.assign_advice(
                    || "select result",
                    config.advices[2],
                    0,
                    || v.copied(),
                )?;
                Ok(c)
            },
        )?;
        Ok(out)
    }
}
