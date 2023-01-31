use ff::Field;
use rand;
use std::marker::PhantomData;
use std::ops::{AddAssign};
use std::vec;
use halo2_proofs::circuit::{AssignedCell, Chip, Layouter, Region, SimpleFloorPlanner, Value, layouter};
use halo2_proofs::plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Fixed, Instance, Selector, Expression, Constraints};
use halo2_proofs::poly::Rotation;
use halo2_proofs::{dev::MockProver, pasta::Fp};

#[derive(Debug,Clone)]
struct TwoDVec<F: Field> {
    data: Vec<Vec<F>>,
}

impl<F: Field> TwoDVec<F> {
    pub fn new(a: Vec<Vec<F>>)->Self{

        Self{
            data: a,
     }
    }

}
#[derive(Debug,Clone)]
struct InstVector<F: Field>{
    data: Vec<Column<Instance>>,
    len: usize,
    _marker: PhantomData<F>,

}

impl<F: Field>  InstVector<F>{
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

#[derive(Debug,Clone)]
struct AdviceVector<F: Field>{
    data: Vec<Column<Advice>>,
    len: usize,
    _marker: PhantomData<F>,
}

impl<F: Field>  AdviceVector<F>{
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

#[derive(Debug,Clone)]
struct LogRegConfig<F: Field>{
    image: AdviceVector<F>,
    kernel: AdviceVector<F>,
    inter: AdviceVector<F>,
    y: InstVector<F>,
    selmul: Selector,
    _marker: PhantomData<F>,
}

#[derive(Debug,Clone)]
struct LogRegChip<F: Field>{
    config: LogRegConfig<F>,
    _marker: PhantomData<F>,
}


impl<F:Field> LogRegChip<F>  {
    
    
    pub fn configure(meta: &mut ConstraintSystem<F>) -> LogRegConfig<F> {
        
        let image = AdviceVector::new_adv_vec(meta, imwid, imlen);
        let kernel = AdviceVector::new_adv_vec(meta, kerwid, kerlen);
        let inter = AdviceVector::new_adv_vec(meta, conwid, conlen) ;
        let y = InstVector::new_ins_vec(meta, conwid, conlen);
        let selmul = meta.selector();

  
        meta.create_gate("conv", |meta|{

            let s = meta.query_selector(selmul);

            let mut imgcells = vec![];
            for i in 0..imwid{
                imgcells.push(Vec::new());
                for j in 0..imlen{
                    let buf = meta.query_advice(image.data[i], Rotation(j as i32));
                    imgcells[i].push(buf);
                }
            }

            let mut kercells = vec![];
            for i in 0..kerwid{
                kercells.push(Vec::new());
                for j in 0..kerlen{
                    let buf = meta.query_advice(kernel.data[i], Rotation(j as i32));
                    kercells[i].push(buf);
                }
            }

            let mut concells = vec![];
            for i in 0..conwid{
                concells.push(Vec::new());
                for j in 0..conlen{
                    let buf = meta.query_advice(inter.data[i], Rotation(j as i32));
                    concells[i].push(buf);
                }
            }

            let mut condash = vec![];
            let mut diff = vec![];
            for i in 0..conwid{
                condash.push(vec![]);
                for j in 0..conlen {
                    let mut conval = Expression::Constant(F::ZERO);                 
                    // let mut conval = Expression::Constant(F::ONE);   // A bug to test circuit               
                    for k in 0..kerwid{
                        for l in 0..kerlen{
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
        

        LogRegConfig{
            image,
            kernel,
            inter,
            y,
            selmul,
            _marker: PhantomData,
       }
}

}



#[derive(Debug,Clone)]

struct LogRegCircuit<F: Field>{
    mdata: TwoDVec<F>,
    xdata: TwoDVec<F>,
}

impl<F: Field> Circuit<F> for LogRegCircuit<F>{
    
    type Config = LogRegConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;
    fn without_witnesses(&self) -> Self {
        return self.clone();
    }
    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        LogRegChip::configure(meta)
    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        
        let image = &self.xdata.data;
        let kernel = &self.mdata.data;
        
    
        let convvalue = layouter.assign_region(|| "layer1", |mut region|{
           
            config.selmul.enable(&mut region, 0)?;
            

            let mut imgcells = vec![];
            for i in 0..imwid{
                imgcells.push(Vec::new());
                for j in 0..imlen{

                let i_cell = region.assign_advice(||"image".to_owned()+&i.to_string()+&j.to_string(),
                 config.image.data[i], 
                 j, 
                 || Value::known(image[i][j]))?;
                imgcells[i].push(i_cell);   
                };
            };

            let mut kercells = vec![];
            for i in 0..kerwid{
                kercells.push(Vec::new());
                for j in 0..kerlen{

                let k_cell = region.assign_advice(||"kernel".to_owned()+&i.to_string()+&j.to_string(),
                    config.kernel.data[i], 
                    j, 
                    || Value::known(kernel[i][j]))?;
                kercells[i].push(k_cell);   
                };
            };

            let mut convcells = vec![];
            for i in 0..conwid{
                convcells.push(vec![]);
                for j in 0..conlen {
                    let mut conval = Value::known(F::ZERO);                    
                    for k in 0..kerwid{
                        for l in 0..kerlen{
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
            

            Ok(convcells)


        });

        let yxz = convvalue.unwrap().clone();
        Ok(for i in 0..conwid{
            for j in 0..conlen{
        let xyz = &yxz[i][j];
        layouter.constrain_instance(xyz.cell() , config.y.data[i], j);
         } 
        })
        
      
    }
    
}


// Alter the dims here //

static imlen: usize = 4;
static kerlen: usize = 2;
static conlen: usize = imlen-kerlen+1;
static imwid: usize = 4;
static kerwid: usize = 2;
static conwid: usize = imwid-imwid+1;

fn main(){

    let k = 16;

        let mut rng = rand::thread_rng();
        

        
        // Random Filter
        let mut filter = Vec::new();
        for i in 0..kerwid{
        let mut mvec = Vec::new();
            for j in 0..kerlen{
                let mut buf = Fp::random(&mut rng);
                mvec.push(buf);
         }
         filter.push(mvec);
        }
    
        // Random Image
        let mut image = Vec::new();
        for i in 0..imwid{
        let mut xvec = Vec::new();
            for j in 0..imlen{
                let mut buf = Fp::random(&mut rng);
                xvec.push(buf);
         }
         image.push(xvec);
        }

        // Calculating Output

        let mut convimage = vec![];
        for i in 0..conwid{
            convimage.push(Vec::new());
            for j in 0..conlen {
                let mut conval = Fp::ZERO;
                for k in 0..kerwid{
                    for l in 0..kerlen{
                        conval.add_assign(image[i+k][j+l].clone().mul(&filter[k][l]));
                    }
                }
            convimage[i].push(conval);
            }
        }
        
        // Wrong Output

        let mut wrongconvimage = vec![];
        for i in 0..conwid{
            wrongconvimage.push(Vec::new());
            for j in 0..conlen {
                let mut conval = Fp::ONE; // Bug Here
                for k in 0..kerwid{
                    for l in 0..kerlen{
                        conval.add_assign(image[i+k][j+l].clone().mul(&filter[k][l]));
                    }
                }
            wrongconvimage[i].push(conval);
            }
        }
        

        let circuit = LogRegCircuit {
            mdata: TwoDVec::new(filter),
            xdata: TwoDVec::new(image),
        };

        let public_input = convimage; // wrongconvimage use this for testing
        let prover = MockProver::run(k, &circuit, public_input.clone());
        // prover.unwrap().assert_satisfied();
        match prover.unwrap().verify(){
            Ok(()) => { println!("Yes proved!")},
            Err(_) => {println!("Not proved!")}

        }
       
}


