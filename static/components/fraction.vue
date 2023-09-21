<template>
	<td class=class>
		<table border=0>
			<tr>
				<td>
					<div class=fraction>
						<div class=numerator>{{numerator == null || numerator.isNaN? 0: numerator}}</div>
						<div class=denominator>{{denominator == null || denominator.isNaN? 0: denominator}}</div>
					</div>
				</td>
				<td> {{operator}} {{fraction.percentage()}}</td>
			</tr>
		</table>
	</td>
</template>

<script>
console.log('import fraction.vue');

export default {
	props : [ 'numerator', 'denominator', 'operator'],
	
    data() {
        return {
        };
    },
    
    computed: {
    	fraction() {
    		var {numerator, denominator} = this;
    		if (numerator == null || numerator.isNaN)
    			numerator = 0;
    		
    		if (denominator == null || denominator.isNaN)
    			denominator = 0;
    		
   			return numerator / denominator;
    	},
    },
    
    created() {
    },
    
    methods: {
    },
    
    mounted(){
    },
    
	directives: {
	},		
    
}

</script>

<style>

.fraction {
    position: relative;
}

.numerator {
    border-bottom: 2px solid black;
    text-align: center;
}

.denominator {
    text-align: center;
}

</style>
