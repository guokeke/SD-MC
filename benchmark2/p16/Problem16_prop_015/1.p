</
  define p: input$=6;
  define q: output$=25;
  define r: output$=22;
  
  alw(!(p and !q and som(q)) or (alw(!r);next (q)))
/>
