<template>
	<div>
		<form name=form method=post enctype="multipart/form-data">
			<template v-if=pn>
				{{upload?'please get': 'update'}} {{pn}}.{{ext}} from <a :href=href_id target=analytics>{{id}}</a> / <a :href=href_pn target=analytics>{{pn_simplified}}</a>, then 
			</template>
			<template v-else>
				please paste your image data here (Ctrl+V), or  
			</template>
			<div class=upload>
	           	choose
	           	<input ref=input name=img type=file @change=change_file>
	           	<input type=hidden name=dataURL :value=dataURL>
	           	<input type=hidden name=pn :value=pn>
	           	<input type=hidden name=lang :value=lang>
	       	</div>
	       	<template v-if=pn>
				and
	       		<input type=submit value=upload>
	       	</template>
		</form>
		
		<div v-if=width>
			<p v-if=pn>
				view <a :href="`/label/tsr.php?pn=${pn}`" target=tsr>tsr result</a>,
				or press <button class=transparent @click=click_delete>delete</button> to remove the file from database;
			</p>
			
			<canvasDragRect ref=canvas tabindex=1 :width=canvas_pysical_width :height=canvas_pysical_height @dblclick=dblclick_img :style="'cursor: ' + zoom" @mousedown=mousedown @mouseup=mouseup @mousemove=mousemove @mouseleave=mouseleave @keydown=keydown></canvasDragRect>
			<img ref=img :src=src :style=style_img :width=width_scale :height=height_scale></img>
		</div>
		<div class=dialog v-if=src_selected :style=style_dialog>
			<template v-if=selectedRegion>
				<p>selected region from the original image is:</p>
				<img :src=src_selected :width="selectedRegion.width * scale" :height="selectedRegion.height * scale"></img>
				<br>
			</template>
			<textarea v-update :rows="1 + output.length" :cols=cols_output :style=style_textarea>{{output.join('\n')}}</textarea>
			<p v-for="latex of output" v-latex v-text="`\\[${latex}\\]`"></p>
		</div>
	</div>
</template>

<script>
import canvasDragRect from "./canvasDragRect.vue"
import {rotateImage} from "../js/image.js"
console.log('import mathocr.vue');

export default {
	components: {canvasDragRect},
	
	props : ['width', 'height', 'pn', 'ext', 'nocache'],
	
	data() {
		return {
			id: '',
			lang: 'en',
			langs : ["CHN_ENG", "ENG", "POR", "FRE", "GER", "ITA", "SPA", "RUS", "JAP", "KOR"],
			deg: 0,
			zoom: 'zoom-out',
			scale : 1,
			src: null,
			upload: false,
			
			text: [[[]]],
			rowspan: {},
			colspan: {},
			align: {},
			valign: {},
			
			codon: [],
			training: 0,
			
			method: 'tableRecognition',
			methods : [],
			
			selectedRegion: null,
			output: [],
			src_selected: null,
		};
	},
	
	async created() {
		this.src = `../../assets/${this.lang}/ocr/${this.ext}/${this.pn}.${this.ext}`;
		if (this.nocache) {
			this.src += "?timestamp=" + new Date().getTime();
		}

		if (this.width){
			console.log("document.body.clientWidth = ", document.body.clientWidth);
			if (this.width < document.body.clientWidth * 0.8){
				this.scale = 1;
				this.zoom = 'zoom-in';
			}
			else{
				this.scale = 0.8;
				this.zoom = 'zoom-out';
			}
		}
		else{
			if (this.width == null){
				this.$root.width = 1000;
				this.$root.height = 768;
			}
		}
	},
	
	computed: {
		dataURL() {
			if ((this.deg / 90) & 1)
				return rotateImage(this.$refs.img, this.width, this.height, this.deg);
		},
	
		translateX() {
			if ((this.deg / 90) & 1)
				return (this.height - this.width) * this.scale / 2;
			return 0;
		},
		
		translateY() {
			return -this.translateX;		
		},
		
		cols_output() {
			if (this.output.length)
				return Math.max(...this.output.map(el => el.length));
			return 20;
		},
		
		style_dialog() {
			if ((this.deg / 90) & 1)
				return `transform: translateY(${this.translateY * 2}px)`;
		},
		
		style_textarea() {
			var width = (this.selectedRegion? this.selectedRegion.width: this.width) * this.scale;
			return `width: ${width}px`;
		},
		
		canvas_pysical_width() {
			if ((this.deg / 90) & 1)
				return this.height_scale;
			return this.width_scale;	
		},
		
		canvas_pysical_height() {
			if ((this.deg / 90) & 1)
				return this.width_scale;
			return this.height_scale;	
		},
		
		width_scale() {
			return this.width * this.scale;
		},
		
		height_scale() {
			return this.height * this.scale;
		},
		
		pn_simplified() {
			return this.pn.match(/^[^$_-]+/)[0];
		},
		
		style_img() {
			return `transform: translate(${this.translateX}px, ${this.translateY}px) rotate(${this.deg}deg);`;
		},		
	},
	
	methods: {
		coordinate_info() {
			var canvas = this.$refs.canvas;
			if (!canvas)
				return '';
			return `{x0 = ${canvas.x0}, y0 : ${canvas.y0}, x1 = ${canvas.x1}, y1 : ${canvas.y1}}`;
		},
	
		readAsDataURL(file, callback) {
			var self = this;
			
			var reader = new FileReader();
			reader.onload = function() {
				var src = this.result;
				
				var image = new Image();
				image.onload = function () {
					self.$root.width = this.width;
					self.$root.height = this.height;
					if (callback) {
						self.$nextTick(callback);
					}
				};
				
				image.src = src;
				self.src = src;
			};

		　　 reader.readAsDataURL(file);
		},
		
		change_file(event){
			var [file] = event.target.files;
			console.log('file.name = ' + file.name);
		　　 this.readAsDataURL(file, this.recognize);
		},
		
		dblclick_img(event){
			if (this.zoom == 'zoom-out'){
				this.zoom = 'zoom-in';
				this.scale *= 0.8;
			}
			else{
				this.zoom = 'zoom-out';
				this.scale /= 0.8;
			}
		},		
		
		async click_delete(event){
			var {pn, ext} = this;
			var ret = await form_post('tsr/delete.php', {pn, ext});
			console.log("status code from tsr/delete.php =", ret);
			this.src = '';
		},
		
		keydown(event){
			switch (event.key){
			case 'L':
			case 'l':
				if (event.ctrlKey){
					this.deg -= 90;
					event.preventDefault();
				}
				break;
				
			case 'R':
			case 'r':
				if (event.ctrlKey){
					this.deg += 90;
					event.preventDefault();
				}
				
				break;
				
			case 'S':
			case 's':
				if (event.ctrlKey){
					event.preventDefault();
					form.submit();
				}
				
				break;
			}
		},	
		
		mousedown(event) {
			if (!event.shiftKey)
				return;
			
			var canvas = this.$refs.canvas;
			if (canvas.flag)
				return;
			
			canvas.mousedown(event);
		},

		mousemove(event){
			var canvas = this.$refs.canvas;
			if (!canvas.flag)
				return;
			
			canvas.mousemove(event);
		},
		
		mouseup(event){
			var canvas = this.$refs.canvas;
			if (!canvas.flag)
				return;

			this.selectedRegion = canvas.getSelectedRegion();
			
	    	var width = Math.min(this.selectedRegion.width * 2, this.width_scale);
			var height = Math.min(this.selectedRegion.height * 3, this.height_scale);
			
	    	var left = (this.width_scale - width) / 2 + this.$refs.img.getScrollLeft();
	    	var top = (this.height_scale - height) / 2 + this.$refs.img.getScrollTop();
	    	
			this.selectedRegion.x /= this.scale;
			this.selectedRegion.y /= this.scale;
			this.selectedRegion.width /= this.scale;
			this.selectedRegion.height /= this.scale;
			
			canvas.mouseup(event);
			
			this.drawImage();
		},
		
		mouseleave(event){
			this.mouseup(event);
			var canvas = this.$refs.canvas;
			if (canvas.flag){
				canvas.mouseleave(event);
			}
		},
		
		recognize(event){
			this.selectedRegion = null;		
			var selectedRegion = {width: this.width, height:this.height, x:0, y:0};
			
	    	var width = Math.min(selectedRegion.width * 2, this.width_scale);
			var height = Math.min(selectedRegion.height * 3, this.height_scale);
			
	    	var left = (this.width_scale - width) / 2 + this.$refs.img.getScrollLeft();
	    	var top = (this.height_scale - height) / 2 + this.$refs.img.getScrollTop();
	    	
			selectedRegion.x /= this.scale;
			selectedRegion.y /= this.scale;
			selectedRegion.width /= this.scale;
			selectedRegion.height /= this.scale;
			
			this.drawImage(selectedRegion);
		},
		
		async drawImage(selectedRegion){
			selectedRegion ||= this.selectedRegion;
			var {x, y, width, height} = selectedRegion;
			
			var canvas = document.createElement('canvas');
			
			canvas.width = width;
			canvas.height = height;
			var ctx = canvas.getContext("2d");
			console.log(x, y, width, height);
			ctx.clearRect(0, 0, width, height);
			
			if ((this.deg / 90) & 1) {
				[x, y] = [y - this.translateX - this.translateY, this.height - x - width];
				ctx.translate(width, 0);
				ctx.rotate(this.deg * Math.PI / 180);
				[width, height] = [height, width];
			}
			else if ((this.deg / 180) & 1){
				[x, y] = [this.width - x - width, this.height - y - height];
				ctx.translate(width, height);
				ctx.rotate(this.deg * Math.PI / 180);
			}
			
			ctx.drawImage(this.$refs.img, x, y, width, height, 0, 0, width, height);	
			
			var ext = this.ext;
			if (ext == 'jpg')
				ext = 'jpeg';
			
			var im_dataurl = canvas.toDataURL(`image/${ext}`);
			var res = await form_post('http://192.168.18.102:5001/image-latex/parser', {im_dataurl, ext});
			console.log(res);
			var {latex} = res;
			this.output = [latex];
			this.src_selected = im_dataurl;
			console.log(this.output);
		},
		
		paste(event){
			var [item] = event.clipboardData.items;
			console.log(item.type);
			this.readAsDataURL(item.getAsFile(), this.recognize);
		},
	},
	
	mounted() {
		var body = document.body;
		
		body.addEventListener("paste", event => {
			event.stopPropagation();
			event.preventDefault();
			this.paste(event);
		});
	},
	
	directives: {
		update: {
		    // after dom is inserted into the document
		    mounted(el, binding) {
		    	el.focus();
		    },
		    
		    updated(el, binding) {
		    	console.log("updated(el, binding) {");
		    	el.value = binding.instance.output.join('\n');
		    	el.focus();
		    },
		},
		
		latex
	},		
}
		
</script>

<style>
img {
	-webkit-user-select: none;
	margin: auto;	
	background-color: hsl(0, 0%, 90%);
	transition: background-color 300ms;
}

body {
	background-color: rgb(199, 237, 204);
	margin-left: 1.5em;
}

input[type=file] {
	color: transparent;
	
	height: 130%;
	width: 6.4em;
	
	position: absolute;
	
	bottom:0;
	left:0;
	right: 0;
	top: 0;	
	
	font-size: 100px;
	
	z-index:1;
	opacity:0;
	filter: alpha(opacity=0);	
	-ms-filter: alpha(opacity=0);
}

.upload {
	position: relative;
	display: inline-block;
	overflow: hidden;
	
	width:100px;
	height:30px;	
	line-height:30px;
	
	top: 10px;
	
	border:1px solid #ddd;
	background:#f6f6f6;
	text-align:center;
	
	color:#333;
	
	font-size: 25px;
}

div.dialog {
	background-color:rgb(199, 237, 204);
}

button.transparent {
	background-color: inherit;
	border-style: none;
	outline: none;
	font-size: 1.5em;
	background-color: white;
}

button.transparent:hover{
	background-color: red;
}

</style>