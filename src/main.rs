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
struct OneDVec<F: Field> {
    data: Vec<F>,
}

impl<F: Field> OneDVec<F> {
    pub fn new(a: Vec<F>)->Self{
        Self{
            data: a,
     }
    }

}
#[derive(Debug,Clone)]
struct AdviceVector<F: Field>{
    data: Column<Advice>,
    len: usize,
    _marker: PhantomData<F>,

}

impl<F: Field>  AdviceVector<F>{
    pub fn new_adv_vec(meta: &mut ConstraintSystem<F>, len: usize) -> AdviceVector<F>{

    
            let buf = meta.advice_column();
            meta.enable_equality(buf);
        

            Self {
                data: buf,
                len,
                _marker: PhantomData,
            }
        }
    }

    #[derive(Debug,Clone)]
    struct InstVector<F: Field>{
        data: Column<Instance>,
        len: usize,
        _marker: PhantomData<F>,
    
    }
    
    impl<F: Field>  InstVector<F>{
        pub fn new_ins_vec(meta: &mut ConstraintSystem<F>, len: usize) -> InstVector<F>{
    
        
                let buf = meta.instance_column();
                meta.enable_equality(buf);
            
    
                Self {
                    data: buf,
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
        
        let image = AdviceVector::new_adv_vec(meta, imlen);
        let kernel = AdviceVector::new_adv_vec(meta, kerlen);
        let inter = AdviceVector::new_adv_vec(meta, conlen) ;
        let y = InstVector::new_ins_vec(meta, conlen);
        let selmul = meta.selector();

  
        meta.create_gate("conv", |meta|{

            let s = meta.query_selector(selmul);

            let mut im = vec![];
            for i in 0..imlen{
                let buf = meta.query_advice(image.data, Rotation(i as i32));
                im.push(buf);
            }
            let mut ker = vec![];
            for j in 0..kerlen{
                let buf = meta.query_advice(kernel.data, Rotation(j as i32));
                ker.push(buf);
            }
            let mut con = vec![];
            for i in 0..conlen{
                let buf = meta.query_advice(inter.data, Rotation(i as i32));
                con.push(buf);
            }

            let mut condash = vec![];
            let mut diff = vec![];
            for i in 0..conlen{
            let mut cal_conv = Expression::Constant(F::ZERO);
            for j in 0..kerlen{
                let xyz = im[i+j].clone();
                let yxz = ker[j].clone();
                cal_conv = cal_conv + (xyz*yxz);

            }
            condash.push(cal_conv);
            let buf = condash[i].clone() - (con[i].clone());
            diff.push(buf)

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
    mdata: OneDVec<F>,
    xdata: OneDVec<F>,
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
            for i in 0..imlen{

                let i_cell = region.assign_advice(||"image".to_owned()+&i.to_string(),
                 config.image.data, 
                 i, 
                 || Value::known(image[i]))?;
                imgcells.push(i_cell);   
            };

            let mut kercells = vec![];
            for j in 0..kerlen{
                let k_cell = region.assign_advice(||"kernel".to_owned()+&j.to_string(),
                 config.kernel.data, 
                 j, 
                 || Value::known(kernel[j]))?;
                kercells.push(k_cell);   
            };

            let mut convcells = vec![];
            for i in 0..conlen{

                let mut buf_image = vec![];
                let mut convop = Value::known(F::ZERO);
                for j in 0..kerlen{
                    let xyz = &imgcells[i+j];
                    buf_image.push(xyz);
                }
                for k in 0..kerlen{
                    convop = convop + (buf_image[k].value().copied() * kercells[k].value());
                }                
                let con_cell = region.assign_advice(||"conv".to_owned()+&i.to_string(),
                 config.inter.data, 
                 i, 
                 || convop)?;
                convcells.push(con_cell);   
            };
            

            

            Ok(convcells)


        });

        let yxz = convvalue.unwrap().clone();
        Ok(for i in 0..conlen{
        let xyz = &yxz[i];
        layouter.constrain_instance(xyz.cell() , config.y.data, i);
        })
        
      
    }
    
}

static imlen: usize = 16;
static kerlen: usize = 9;
static conlen: usize = imlen-kerlen+1;


fn main(){

    let k = 16;

        let mut rng = rand::thread_rng();
        let mut mvec = Vec::new();
        let mut xvec = Vec::new();
        let mut yvec = Vec::new();
        for i in 0..kerlen{
            let mut buf = Fp::random(&mut rng);
            mvec.push(buf);
        }
    
        for i in 0..imlen{
            let buf = Fp::random(&mut rng);
            xvec.push(buf);
        }
        
        for i in 0..conlen{
            let mut z = Fp::ZERO;
            for j in 0..kerlen{
                z.add_assign(xvec[i+j].clone().mul(&mvec[j]));
            }
            yvec.push(z);
        }

        let circuit = LogRegCircuit {
            mdata: OneDVec::new(mvec),
            xdata: OneDVec::new(xvec),
        };

        let public_input = yvec;
        let prover = MockProver::run(k, &circuit, vec![public_input.clone()]);
        prover.unwrap().assert_satisfied();
        // match prover.unwrap().verify(){
        //     Ok(()) => { println!("Yes proved!")},
        //     Err(_) => {println!("Not proved!")}

        // }
       
}


