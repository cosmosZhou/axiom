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


# IDE for online-debugging
In future, an online IDE with debugging functionality will be developed, based on the following projects:  
https://github.com/coder/code-server  
https://github.com/eclipse-theia/theia  
https://github.com/jupyterlab/jupyterlab  
https://github.com/sagemathinc/cocalc  

# latex
function: $f(x)=\frac{P(x)}{Q(x)}$


$$
X(m,n)=
\begin{cases}
x(n),\\
x(n-1),\\
x(n+1)
\end{cases}
$$

# multiprocessing debugging 
## VSCode
* debug the single-process program run.py using .vscode/launch.json where name = "Python: Current File"
* debug the multiprocessing program run.py using .vscode/launch.json where name = "Python: run.py"

## PyCharm
* In Settings (Ctrl+Alt+S)(File | Settings | Build, Execution, Deployment | Python Debugger): make these settings:

 | Option                                            | Config             |
 |---------------------------------------------------|--------------------| 
 | gevent compatible                                 | :x:                |
 | Attach to subprocess automatically when debugging | :white_check_mark: |
* Set Breakpoint, make sure it is set with the following property (Ctrl+Shift+F8):

 | Option    | Config             |
 |-----------|--------------------| 
 | Enabled   | :white_check_mark: |
 | Suspended | Thread             |
 | Condition |                    |
* make necessary settings in Python Debug Configurations:

 | Option                      | Config                           |
 |-----------------------------|----------------------------------| 
 | Name                        | run.py                           |
 | Python interpreter          | a local Python interpreter       |
 | Run Python script or module | script                           |
 | script                      | $ProjectFileDir$/run.py          |
 | Script parameters           | --parallel --debug --processes=4 |
 | Working directory           | $ProjectFileDir$                 |
* press Shift+F9 to start multiprocessing debugging 