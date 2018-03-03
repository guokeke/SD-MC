</
  define p: input$=3;
  define q: output$=22;
  define r: output$=23;
  
  alw(!(p and !q) or (alw(!r);next (q)) or alw(!r))
/>
