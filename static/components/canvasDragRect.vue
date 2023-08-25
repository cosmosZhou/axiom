<template>
	<canvas :width=width :height=height></canvas>
</template>

<script>
console.log('import canvasDragRect.vue');
import Canvas from "../js/Canvas.js"

export default {
	props : ['width', 'height'],
	
	data(){
		return {
			flag: false,
			canvas: new Canvas(null, null, null, null, 'blue'),
		};
	},
	
	created(){
	},
	
	computed: {
		x0: {
			get(){
				return this.canvas.x0;	
			},
				
			set(x0){
				this.canvas.x0 = x0;
				this.canvas.clear_cache();
			}
		},
		
		y0: {
			get(){
				return this.canvas.y0;	
			},
				
			set(y0){
				this.canvas.y0 = y0;
				this.canvas.clear_cache();
			}
		},
		
		x1: {
			get(){
				return this.canvas.x1;	
			},
				
			set(x1){
				this.canvas.x1 = x1;
				this.canvas.clear_cache();
			}
		},
		
		y1: {
			get(){
				return this.canvas.y1;	
			},
				
			set(y1){
				this.canvas.y1 = y1;
				this.canvas.clear_cache();
			}
		},
		
		color: {
			get(){
				return this.canvas.color;	
			},
				
			set(color){
				this.canvas.color = color;
			}
		},
		
		ctx(){
			return this.$el.getContext("2d");
		},		
	},
	
	methods: {
		getSelectedRegion(){
			var [left, top] = this.leftTop();
			var {x0, y0} = this;
			var x = x0 - left;
			var y = y0 - top;
			var width = this.canvas.dx;
			var height = this.canvas.dy;
			if (width < 0){
				x += width + 1;
				width = -width;
			}
			
			if (height < 0){
				y += height + 1;
				height = -height;
			}
			return {x, y, width, height};
		},
		
		leftTop(){
			var rect = this.$el.getBoundingClientRect();
			return [rect.x, rect.y];
		},
		
		drawDashedLine(x0, y0, x1, y1){
			this.canvas.set_color(this.ctx);
			this.canvas.clearDashedLine(this.ctx);
			
			this.x0 = x0;
			this.y0 = y0;
			this.x1 = x1;
			this.y1 = y1;
			this.canvas.drawDashedLine(this.ctx);
		},
		
		redrawRect(x1, y1, x0, y0){
			this.canvas.set_color(this.ctx);
			this.canvas.clearRect(this.ctx, x0, y0);
			
			this.x1 = x1;
			this.y1 = y1;
			
			this.canvas.drawRect(this.ctx, x0, y0);
		},

		mousemove(event){
			//console.log("in canvas DrawgRect: mousemove(event){");
			if(this.flag){
				this.redrawRect(event.x, event.y, ...this.leftTop());
			}

			event.preventDefault();
		},

		mousedown(event){
			if (!event.shiftKey)
				return;
			this.init(event.x, event.y);
			event.preventDefault();
		},
		
		mouseup(event){
			this.mouseleave(event);
			this.canvas.clearRect(this.ctx, ...this.leftTop());
		},
		
		mouseleave(event){
			this.flag = false;
			event.preventDefault();
		},
		
		init(x, y){
			if (this.x1 != null){
				this.canvas.clearRect(this.ctx, ...this.leftTop());
			}

			this.x0 = x;
			this.y0 = y;
			
			this.flag = true;
			
			this.x1 = null;
			this.y1 = null;
		},
	},
}

</script>

<style scoped>
canvas{
	background-color: transparent;
	position: absolute;
	z-index: 2;
}
</style>