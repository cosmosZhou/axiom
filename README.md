# axiom

reference website:

http://www.axiom.top

latex is printed with the aid of the following project:

http://docs.mathjax.org/en/latest/  
https://github.com/mathjax/MathJax.git  

python is edited with the aid of the following project:

https://codemirror.net/5/  
https://github.com/codemirror/codemirror5  


# representation of html files
## requirements
python >= 3.10

pip install sympy.keras
## scripts to generate visualized html
git clone --depth=1 https://github.com/cosmosZhou/axiom.git  
cd axiom  
python run.py  

you'll get the following output:   
in all 4069 axioms  
plausible:  
.\axiom\stats\distributed\imply\et\eq.py  
./target/stats/distributed/imply/et/eq.html  

.\axiom\discrete\eq\eq_matmul\eq_piece\imply\eq\matmul\PLU.py  
./target/discrete/eq/eq_matmul/eq_piece/imply/eq/matmul/PLU.html  

.\axiom\stats\eq_inverse\imply\et\eq.py  
./target/stats/eq_inverse/imply/et/eq.html  

.\axiom\keras\eq_conditioned\eq_expect\eq_expect\imply\et\eq\expect\Bellman\optimality.py  
./target/keras/eq_conditioned/eq_expect/eq_expect/imply/et/eq/expect/Bellman/optimality.html  

seconds costed = 91.74423789978027  
minutes costed = 1.5290706316630045  
total plausible = 4  
total failed    = 0  


open the folder target, and then you can browse the visualized structure of python and latex of axioms and theorems.  
to debug one single file, execute the following command:  
python run.py discrete.binom.to.add.Pascal  
or try to open and execute the python file directly:   
.\axiom\discrete/binom/to/add/Pascal.py  


#online IDE
https://github.com/eclipse-theia/theia  
https://github.com/jupyterlab/jupyterlab  
https://github.com/sagemathinc/cocalc  