<template>
    <div class=packageSelector-wrapper tabindex=1 @keydown=keydown>
        move <font color=blue>{{theorem}}</font> to :
        <p>{{path}}</p>
        <div class=packageSelector>
            <smallPackage v-for="module, i of packages" :module=module :tabindex="i + 1"></smallPackage>
        </div>
        
        <button class=confirm type=button @click=click>confirm</button>
        <button class=cancel type=button @click=click>cancel</button>
    </div>

</template>

<script>
import smallPackage from "./smallPackage.vue"
console.log('import packageSelector.vue');

export default {
    data() {
        return {
        	packages: [],
        };
    },
    
    components : {smallPackage},

    async created() {
        var sympy = axiom_user();
		var packages = await get(`/${sympy}/php/request/scandir.php`, {folder: this.path});
		this.packages = packages;
    	console.log("in created() {: ", this.packages);
    },
    
    props : [ 'path'],
    
    computed: {            
        theorem() {
            var children = this.$parent.children;
            var index = this.$parent.focusedIndex;
            return children[index].$el.textContent.trim();
        },        
    },
    
    methods: {		
        click(event){
            var self = event.target;
            switch (self.className){
            case 'confirm':
                var oldFile = location.href.match(/\/index.php\/(.+)/)[1];
                if (!oldFile.endsWith('/')){
                    oldFile += '/';
                }
                oldFile += this.theorem;
                
                var user = axiom_user();
                var params = {
                    theorem: oldFile.replaceAll('/', '.'), 
                    dest: this.path.replaceAll('/', '.').substring(1),
                };
                
                parent = this.$parent;
                form_post(`/${user}/php/request/move/theorem.php`, params).then(res =>{
                    console.log("res = " + res);
                    var focusedIndex = this.$parent.focusedIndex;
                    //console.log('this.$parent.theorems = ' + this.$parent.theorems);
                    this.$parent.theorems.delete(focusedIndex);
                    //console.log('this.$parent.theorems = ' + this.$parent.theorems);
                    this.$parent.focusedIndex = -1;                        
                });
                
                break;
            case 'cancel':
                break;
            }            
        },
        
        focus(module){                
            if (module != null){                                    
                for (let child of this.children){
                    if (child.module == module){
                        child.$el.focus();
                        break;
                    }
                }
            }
            else{
                self = this;    
            
                setTimeout(()=>{
                    for (let child of self.children){
                        child.$el.focus();
                        break;
                    }
                    
                }, 100);                
            }
        },
        
        keydown(event) {                
            var self = event.target;
            var key = event.key;

            switch (key) {
                case 'ArrowLeft':
                    break;
                case 'ArrowRight':
                    break;
                case 'ArrowDown':
                    break;
                case 'ArrowUp':
                    break;    
                case 'Home':
                    break;                        
                case 'End':
                    break;
                case 'Backspace':
                    console.log("case 'Backspace': in package-selector.vue");
                    this.path = this.path.match(/(.*)\.\w+/)[1];
                    
                    this.focus();
                    break;
                default:
                    if (key.length == 1) {
                    }
                    break;
            }                
        },
        
    }
}
</script>

<style>

div>div.packageSelector{
    background-color: rgb(199, 237, 204);
    position: absolute; 
    border: 1px solid #555; 
    width: 600px; 
    height: 400px;
    z-index: 10;
    padding: 7px 1px 7px 7px;
    overflow:auto;  
//    overflow-x:hidden;
//    overflow-y:hidden;
}

div button{
    position: relative; 
    bottom: 7px;
    z-index: 11;
}

div button.confirm{
    left: 220px; 
    top: 420px;
}

div button.cancel{
    left: 260px; 
    top: 420px;
}

div.packageSelector-wrapper{
    position: absolute;
    left: 436px;
    top: 207px; 
}

div.packageSelector-wrapper:focus {
    outline: none;
}

</style>