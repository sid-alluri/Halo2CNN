use halo2_proofs::arithmetic::{FieldExt, Group};
use rand::{self, Rng};
use std::marker::PhantomData;
use std::ops::{AddAssign};
use std::vec;
use halo2_proofs::circuit::{Layouter, SimpleFloorPlanner, Value};
use halo2_proofs::plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Instance, Selector, Expression, Constraints, TableColumn};
use halo2_proofs::poly::Rotation;
use halo2_proofs::{dev::MockProver, pasta::Fp};
use std::time::{Duration, Instant};


// Considering a random image and filter with below dimensions 

static IMLEN: usize = 8;
static KERLEN: usize = 3;
static CONLEN: usize = IMLEN-KERLEN+1;
static IMWID: usize = 8;
static KERWID: usize = 8;
static CONWID: usize = IMWID-KERWID+1;
static MAX_CONV_VAL: usize =  255*5*KERLEN*KERWID; // max possible positive number in conv operation.

// pixel range = [0,255]
// kernel range = [-5,5]

#[derive(Debug,Clone)]
struct TwoDVec<F: FieldExt> {
    data: Vec<Vec<F>>,
}

impl<F: FieldExt> TwoDVec<F> {
    pub fn new(a: Vec<Vec<F>>)->Self{

        Self{
            data: a,
     }
    }

}

// Instance Vector

#[derive(Debug,Clone)]
struct InstVector<F: FieldExt>{
    data: Vec<Column<Instance>>,
    len: usize,
    _marker: PhantomData<F>,

}

impl<F: FieldExt>  InstVector<F>{
    pub fn new_ins_vec(meta: &mut ConstraintSystem<F>, vec_size: usize, len: usize) -> InstVector<F>{

        let mut instbufarr = vec![];
        for _i in 0..vec_size{
                let buf = meta.instance_column();
                meta.enable_equality(buf);
                instbufarr.push(buf);
            }

            Self {
                data: instbufarr,
                len,
                _marker: PhantomData,
            }
        }
    }

// Advice Vector

#[derive(Debug,Clone)]
struct AdviceVector<F: FieldExt>{
    data: Vec<Column<Advice>>,
    len: usize,
    _marker: PhantomData<F>,
}

impl<F: FieldExt>  AdviceVector<F>{
    pub fn new_adv_vec(meta: &mut ConstraintSystem<F>, vec_size: usize, len: usize) -> AdviceVector<F>{
        let mut advbufarr = vec![];
        for _i in 0..vec_size{
                let buf = meta.advice_column();
                meta.enable_equality(buf);
                advbufarr.push(buf);
            }

            Self {
                data: advbufarr,
                len,
                _marker: PhantomData,

            }
        }
    }

// Lookup Table: [0:MAXCONVVALUE]

// Contains all possible positive values, output of a ReLU function should belong to this table

#[derive(Debug, Clone)]
struct ReLULoookUp<F: FieldExt> {
        relop: TableColumn,
        _marker: PhantomData<F>,
}
impl<F: FieldExt> ReLULoookUp<F> {
        fn configure(meta: &mut ConstraintSystem<F>) -> Self {
            let relop = meta.lookup_table_column();
    
            Self {
                relop,
                _marker: PhantomData,
            }
        }
        fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
            layouter.assign_table(
                || "relu lookup table",
                |mut table| {
                    let range = MAX_CONV_VAL as i32;
                    let mut offset = 0;
                    for i in 0..=range {
                            table.assign_cell(
                                || "relop",
                                self.relop ,
                                offset,
                                || Value::known(F::from(i as u64)),
                            )?;
                        
                    offset += 1; 
                    }
    
                    Ok(())
                },
            )
        }
    }

#[derive(Debug,Clone)]
struct LogRegConfig<F: FieldExt>{
    image: AdviceVector<F>,
    kernel: AdviceVector<F>,
    inter: AdviceVector<F>,
    relu: AdviceVector<F>,
    y: InstVector<F>,
    selmul: Selector,
    selrel: Selector,
    reltable: ReLULoookUp<F>,
    _marker: PhantomData<F>,
}


#[derive(Debug,Clone)]
struct LogRegChip<F: FieldExt>{
    config: LogRegConfig<F>,
    _marker: PhantomData<F>,
}


impl<F:FieldExt> LogRegChip<F>  {
    
    
    pub fn configure(meta: &mut ConstraintSystem<F>) -> LogRegConfig<F> {
        
        let image = AdviceVector::new_adv_vec(meta, IMWID, IMLEN);
        let kernel = AdviceVector::new_adv_vec(meta, KERWID, KERLEN);
        let inter = AdviceVector::new_adv_vec(meta, CONWID, CONLEN) ;
        let relu = AdviceVector::new_adv_vec(meta, CONWID, CONLEN) ;
        let y = InstVector::new_ins_vec(meta, CONWID, CONLEN);
        let selmul = meta.selector();

  
        let selrel = meta.complex_selector();
        let reltable  = ReLULoookUp::configure(meta);

        meta.create_gate("conv", |meta|{

            let s = meta.query_selector(selmul);

            let mut imgcells = vec![];
            for i in 0..IMWID{
                imgcells.push(Vec::new());
                for j in 0..IMLEN{
                    let buf = meta.query_advice(image.data[i], Rotation(j as i32));
                    imgcells[i].push(buf);
                }
            }

            let mut kercells = vec![];
            for i in 0..KERWID{
                kercells.push(Vec::new());
                for j in 0..KERLEN{
                    let buf = meta.query_advice(kernel.data[i], Rotation(j as i32));
                    kercells[i].push(buf);
                }
            }

            let mut concells = vec![];
            for i in 0..CONWID{
                concells.push(Vec::new());
                for j in 0..CONLEN{
                    let buf = meta.query_advice(inter.data[i], Rotation(j as i32));
                    concells[i].push(buf);
                }
            }

            let mut condash = vec![];
            let mut diff = vec![];
            for i in 0..CONWID{
                condash.push(vec![]);
                for j in 0..CONLEN {
                    let mut conval = Expression::Constant(F::zero());                 
                    // let mut conval = Expression::Constant(F::one());   // A bug                
                    for k in 0..KERWID{
                        for l in 0..KERLEN{
                            conval = conval + (imgcells[i+k][j+l].clone()*kercells[k][l].clone());
                        }
                    }
                condash[i].push(conval);   
                let buf = condash[i][j].clone() - (concells[i][j].clone());
                diff.push(buf);
            }
            
        }
        Constraints::with_selector(s, diff)   
        });
        
  
            for i in 0..CONWID{
                for j in 0..CONLEN{

                    meta.lookup(|meta| {
                        let mut  diff = vec![];
                        let selrel = meta.query_selector(selrel);
                        
                        let valueop = meta.query_advice(relu.data[i], Rotation(j as i32));

                    diff.push((selrel.clone()*valueop , reltable.relop));

                    diff
                     });

                }
            }

        LogRegConfig{
            image,
            kernel,
            inter,
            relu,
            y,
            selmul,
            selrel,
            reltable,
            _marker: PhantomData,
       }
}

}



#[derive(Debug,Clone)]

struct LogRegCircuit<F: FieldExt>{
    mdata: TwoDVec<F>,
    xdata: TwoDVec<F>,
}

impl<F: FieldExt> Circuit<F> for LogRegCircuit<F>{
    
    type Config = LogRegConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;
    fn without_witnesses(&self) -> Self {
        return self.clone();
    }
    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        LogRegChip::configure(meta)
    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        
        config.reltable.load(&mut layouter)?;
        let image = &self.xdata.data;
        let kernel = &self.mdata.data;
        
        
    
        let cnn = layouter.assign_region(|| "layer1", |mut region|{
           
            config.selmul.enable(&mut region, 0)?;
            

            let mut imgcells = vec![];
            for i in 0..IMWID{
                imgcells.push(Vec::new());
                for j in 0..IMLEN{

                let i_cell = region.assign_advice(||"image".to_owned()+&i.to_string()+&j.to_string(),
                 config.image.data[i], 
                 j, 
                 || Value::known(image[i][j]))?;
                imgcells[i].push(i_cell);   
                };
            };

            let mut kercells = vec![];
            for i in 0..KERWID{
                kercells.push(Vec::new());
                for j in 0..KERLEN{

                let k_cell = region.assign_advice(||"kernel".to_owned()+&i.to_string()+&j.to_string(),
                    config.kernel.data[i], 
                    j, 
                    || Value::known(kernel[i][j]))?;
                kercells[i].push(k_cell);   
                };
            };

            let mut convcells = vec![];
            for i in 0..CONWID{
                convcells.push(vec![]);
                for j in 0..CONLEN {
                    let mut conval = Value::known(F::zero());                    
                    for k in 0..KERWID{
                        for l in 0..KERLEN{
                            conval = conval + (imgcells[i+k][j+l].value().copied()*kercells[k][l].value());
                        };
                    };
                
                   
                let con_cell = region.assign_advice(||"conv".to_owned()+&i.to_string()+&j.to_string(),
                 config.inter.data[i], 
                 j, 
                 || conval)?;
                convcells[i].push(con_cell);   
            };
            
        };

        config.selrel.enable(&mut region, 0)?;


        let mut relcells = vec![];
            for i in 0..CONWID{
                relcells.push(vec![]);
                for j in 0..CONLEN {
                    let maxconvval = Value::known(F::from(MAX_CONV_VAL as u64));                 
                    let rel_val = convcells[i][j].clone().value().copied().zip(maxconvval).map(|(a,b)| {
                        let  zero = F::zero(); 
                        if a.gt(&b) 
                        {zero} 
                        else 
                        {a}
                    } );
                    // let rel_val = convcells[i][j].clone().value().copied(); // DANGER replace the above equation with this to check the lookup constraints and equality constraints.
                   
                let rel_cell = region.assign_advice(||"relu".to_owned()+&i.to_string()+&j.to_string(),
                 config.relu.data[i], 
                 j, 
                 || rel_val)?;
                relcells[i].push(rel_cell);   
            };
            
        };
            Ok(relcells)


        });

        let buf = cnn.unwrap().clone();
        Ok(for i in 0..CONWID{
            for j in 0..CONLEN{
        let buf1 = &buf[i][j];
        layouter.constrain_instance(buf1.cell() , config.y.data[i], j);
         } 
        })
        
      
    }
    
}

fn main(){

    let k = 16; // Alter based on # of rows

        let mut rng = rand::thread_rng();
        
        // Random Filter
        let mut filter = Vec::new();
        for i in 0..KERWID{
        let mut mvec = Vec::new();
            for j in 0..KERLEN{
                let mut buf = Fp::zero();
                let random_value:f32 = rng.gen_range(-5.0..=5.0);
                let x = random_value.round() as i32;
                if x < 0
                { buf = Fp::from(x as u64);
                buf = buf.neg();} 
               else 
               { buf = Fp::from(x as u64);} 
               mvec.push(buf);
         }
         filter.push(mvec);
        }
    

        // Random Image
        let mut image = Vec::new();
        for i in 0..IMWID{
        let mut xvec = Vec::new();
            for j in 0..IMLEN{
                let x = rng.gen_range(0..=255);
                let mut buf = Fp::from(x);
                xvec.push(buf);
         }
         image.push(xvec);
        }

        
        // Calculating Output
        let mut convimage = vec![];
        let max_pos_val = Fp::from(MAX_CONV_VAL as u64);
        let zero = Fp::zero();
        for i in 0..CONWID{
            convimage.push(Vec::new());
            for j in 0..CONLEN {
                let mut conval = Fp::zero();
                for k in 0..KERWID{
                    for l in 0..KERLEN{
                        conval.add_assign(image[i+k][j+l].clone().mul(&filter[k][l]));
                    }
                }
            if conval.gt(&max_pos_val) {conval = zero;} else{conval = conval;} //relu
            convimage[i].push(conval);
            }
        }
      

        let circuit = LogRegCircuit {
            mdata: TwoDVec::new(filter),
            xdata: TwoDVec::new(image),
        };

        let public_input = convimage; 

        // MockProver
        let start = Instant::now();
        let prover = MockProver::run(k, &circuit, public_input.clone());
        let duration = start.elapsed();

        // prover.unwrap().assert_satisfied();
        match prover.unwrap().verify(){
            Ok(()) => { println!("Yes proved!")},
            Err(_) => {println!("Not proved!")}

        }
        println!("Time taken by MockProver: {:?}", duration);

            
        }
        




