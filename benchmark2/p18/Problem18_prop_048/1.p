</
  define p: input$=2;
  define q: output$=23;
  define r: output$=24;
  
  alw(!(p and !q) or (alw(!r);next (q)) or alw(!r))
/>
