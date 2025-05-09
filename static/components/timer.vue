<template>
	<div>
		<font color=red>time lapse</font>: {{HHmmss}}
		<p v-if=stop>the timer has stopped!</p>
	</div>
</template>

<script>
console.log('import timer.vue');

export default {
	props: ['cond', 'trigger'],

    components: {},

    data() {
        return {
        	currentTime: 0,
        	startTime: 0,
        	timerID: null,
			pause: false,
        };
    },

    computed: {
    	stop() {
    		var {cond} = this;
    		if (cond)
    			return false;
    		this.clearInterval();
    		if (!this.pause && this.trigger)
    			this.trigger();
    		return true;
    	},

    	HHmmss() {
    		var {seconds} = this;
    		seconds = seconds.round();

    		var minutes = (seconds / 60).floor();
    		seconds %= 60;

    		seconds = seconds.toString().padStart(2, '0');

    		var hours = (minutes / 60).floor();
    		minutes %= 60;

    		if (hours) {
    			return `${hours.toString().padStart(2, '0')}:${minutes.toString().padStart(2, '0')}:${seconds}`;
    		}

    		if (minutes) {
    			return `${minutes.toString().padStart(2, '0')}:${seconds}`;
    		}

    		return `${seconds} seconds`;
    	},

    	seconds() {
    		return this.currentTime - this.startTime;
    	},

    	minutes() {
    		return this.seconds / 60;
    	},

    	hours() {
    		return this.minutes / 60;
    	},
    },

    methods: {
    	clearInterval() {
    		clearInterval(this.timerID);
    	},
    },

    created() {
    },

    mounted() {
		this.startTime = Date.now() / 1000;
		this.currentTime = this.startTime;
        this.timerID = setInterval(() => {
            this.currentTime = Date.now() / 1000;
        }, 1000);
		var {repeat} = this.$parent.kwargs.kwargs;
		if (repeat) {
			if (typeof repeat == 'object')
				var [[action, minutes]] = Object.entries(repeat);
			else {
				var action = typeof repeat != 'string' || repeat.isInteger? 'reload' : repeat;
				var minutes = 20;
			}
			var self = this;
			console.log(`page will be ${action}ed after ${minutes} minutes`);
			setTimeout(() => {
				if (self.pause)
					return;
				if (action == 'submit')
					document.form.submit();
				else
    				location.reload();
			}, minutes * 60 * 1000); // Reloads the page after 10 minutes
		}
    },

    unmounted() {
    	this.clearInterval();
    },

	directives: {
		focus: {
		    // after dom is inserted into the document
		    mounted(el, binding) {
		    	el.focus();
		    },
		},
	},

}
</script>

<style>
</style>
