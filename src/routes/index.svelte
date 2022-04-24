<script>
  import { Button } from "carbon-components-svelte";
  import { onMount } from 'svelte';
  onMount(async () => {
    var TxtRotate = function(el, toRotate, period) {
  this.toRotate = toRotate;
  this.el = el;
  this.loopNum = 0;
  this.period = parseInt(period, 10) || 2000;
  this.txt = '';
  this.tick();
  this.isDeleting = false;
};

TxtRotate.prototype.tick = function() {
  var i = this.loopNum % this.toRotate.length;
  var fullTxt = this.toRotate[i];

  if (this.isDeleting) {
    this.txt = fullTxt.substring(0, this.txt.length - 1);
  } else {
    this.txt = fullTxt.substring(0, this.txt.length + 1);
  }

  this.el.innerHTML = '<span class="wrap">'+this.txt+'</span>';

  var that = this;
  var delta = 300 - Math.random() * 100;

  if (this.isDeleting) { delta /= 2; }

  if (!this.isDeleting && this.txt === fullTxt) {
    delta = this.period;
    this.isDeleting = true;
  } else if (this.isDeleting && this.txt === '') {
    this.isDeleting = false;
    this.loopNum++;
    delta = 500;
  }

  setTimeout(function() {
    that.tick();
  }, delta);
};

window.onload = function() {
  var elements = document.getElementsByClassName('txt-rotate');
  for (var i=0; i<elements.length; i++) {
    var toRotate = elements[i].getAttribute('data-rotate');
    var period = elements[i].getAttribute('data-period');
    if (toRotate) {
      new TxtRotate(elements[i], JSON.parse(toRotate), period);
    }
  }
  // INJECT CSS
  var css = document.createElement("style");
  css.type = "text/css";
  css.innerHTML = ".txt-rotate > .wrap { border-right: 0.16em solid rgb(255, 0, 212) }";
  document.body.appendChild(css);
};
  });
  

</script>
<style>
  span {
    font-size: x-large;
    font-weight: bold;
    /*color: rgb(255, 0, 212);*/
  }
  h1{
    font-size: 20vh;
  }
  h3 {
    font-style: italic;

  }
</style>
<div id="leftTitle">
<h1>Fides</h1>
<h3>Experimental multi party <br/> hosting solution</h3>
</div>

<div id="rightTitle"><h2>Making dapps more</h2><span
  class="txt-rotate"
  data-period="500"
  data-rotate='[ "trustless", "robust", "distributed"]'></span></div>

<Button>Learn more</Button>
