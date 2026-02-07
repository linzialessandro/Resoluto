use yew::prelude::*;
use resoluto_core::{generate_problem, Difficulty, ProblemType, Problem};
use web_sys::{Event, HtmlSelectElement};
use wasm_bindgen::JsCast;
use wasm_bindgen::closure::Closure;

#[function_component(App)]
fn app() -> Html {
    let problems = use_state(|| Vec::<Problem>::new());
    let count = use_state(|| 5);
    let difficulty = use_state(|| Difficulty::Hard);
    let problem_type = use_state(|| ProblemType::Linear);

    let on_generate = {
        let problems = problems.clone();
        let count = count.clone();
        let difficulty = difficulty.clone();
        let problem_type = problem_type.clone();
        
        Callback::from(move |_| {
            let mut generated = Vec::new();
            for _ in 0..*count {
                let problem = generate_problem(*problem_type, *difficulty);
                generated.push(problem);
            }
            
            problems.set(generated);
        })
    };

    {
        let problems = problems.clone();
        use_effect_with(problems, |_| {
            let interval_id = std::rc::Rc::new(std::cell::RefCell::new(None::<i32>));
            let interval_id_clone = interval_id.clone();
            
            let callback = Closure::wrap(Box::new(move || {
                if let Some(window) = web_sys::window() {
                    // Try to get renderMath function
                    let render = js_sys::Reflect::get(&window, &"renderMath".into());
                    
                    if let Ok(val) = render {
                        if let Ok(func) = val.dyn_into::<js_sys::Function>() {
                             // Call it
                             let result = func.call0(&window).unwrap_or(wasm_bindgen::JsValue::FALSE);
                             
                             // If it returned true (success), clear interval
                             if result.is_truthy() {
                                 if let Some(id) = *interval_id_clone.borrow() {
                                     window.clear_interval_with_handle(id);
                                 }
                             }
                        }
                    }
                }
            }) as Box<dyn FnMut()>);

            if let Some(window) = web_sys::window() {
                let id = window.set_interval_with_callback_and_timeout_and_arguments_0(
                    callback.as_ref().unchecked_ref(),
                    100,
                ).ok();
                *interval_id.borrow_mut() = id;
            }
            
            callback.forget();
            
            move || {
                if let Some(window) = web_sys::window() {
                    if let Some(id) = *interval_id.borrow() {
                        window.clear_interval_with_handle(id);
                    }
                }
            }
        });
    }

    let on_count_change = {
        let count = count.clone();
        Callback::from(move |e: Event| {
            let input: web_sys::HtmlInputElement = e.target_unchecked_into();
            if let Ok(value) = input.value().parse::<usize>() {
                count.set(value.max(1).min(50));
            }
        })
    };

    let on_difficulty_change = {
        let difficulty = difficulty.clone();
        Callback::from(move |e: Event| {
            let select: HtmlSelectElement = e.target_unchecked_into();
            let val = select.value();
            let new_difficulty = match val.as_str() {
                "medium" => Difficulty::Medium,
                "hard" => Difficulty::Hard,
                _ => Difficulty::Easy,
            };
            difficulty.set(new_difficulty);
        })
    };

    let on_type_change = {
        let problem_type = problem_type.clone();
        Callback::from(move |e: Event| {
            let select: HtmlSelectElement = e.target_unchecked_into();
            let val = select.value();
            let new_type = match val.as_str() {
                "linear" => ProblemType::Linear,
                "rational" => ProblemType::Rational,
                "irrational" => ProblemType::Irrational,
                "absolute-value" => ProblemType::AbsoluteValue,
                _ => ProblemType::Quadratic,
            };
            problem_type.set(new_type);
        })
    };

    html! {
        <div class="container">
            <header>
                <img src="logo.png" alt="Resoluto Logo" class="logo" />
                <h1>{"Resoluto"}</h1>
                <p class="subtitle">{"Deterministic Mathematical Problem Generator"}</p>
            </header>

            <div class="controls">
                <div class="control-group">
                    <label for="problem-type">{"Problem Type"}</label>
                    <select id="problem-type" onchange={on_type_change}>
                        <option value="linear" selected={*problem_type == ProblemType::Linear}>{"Linear Equations"}</option>
                        <option value="quadratic" selected={*problem_type == ProblemType::Quadratic}>{"Quadratic Equations"}</option>
                        <option value="rational" selected={*problem_type == ProblemType::Rational}>{"Rational Equations"}</option>
                        <option value="irrational" selected={*problem_type == ProblemType::Irrational}>{"Irrational Equations"}</option>
                        <option value="absolute-value" selected={*problem_type == ProblemType::AbsoluteValue}>{"Absolute Value Equations"}</option>
                    </select>
                </div>

                <div class="control-group">
                    <label for="difficulty">{"Difficulty"}</label>
                    <select id="difficulty" onchange={on_difficulty_change}>
                        <option value="easy" selected={*difficulty == Difficulty::Easy}>{"Easy"}</option>
                        <option value="medium" selected={*difficulty == Difficulty::Medium}>{"Medium"}</option>
                        <option value="hard" selected={*difficulty == Difficulty::Hard}>{"Hard"}</option>
                    </select>
                </div>

                <div class="control-group">
                    <label for="count">{"Number of Problems"}</label>
                    <input 
                        id="count"
                        type="number" 
                        value={count.to_string()} 
                        onchange={on_count_change}
                        min="1"
                        max="50"
                    />
                </div>

                <button class="generate-btn" onclick={on_generate}>
                    {"Generate Problems"}
                </button>
            </div>

            {if !problems.is_empty() {
                html! {
                    <div class="output">
                        <div class="section">
                            <h2>{"Exercises"}</h2>
                            <ol>
                                {for problems.iter().enumerate().map(|(i, p)| html! {
                                    <li key={format!("prob-{}-{}", i, p.to_latex())} class="problem">
                                        <span class="latex">{format!("\\({}\\)", p.to_latex())}</span>
                                    </li>
                                })}
                            </ol>
                        </div>

                        <div class="section">
                            <h2>{"Solutions"}</h2>
                            <ol>
                                {for problems.iter().enumerate().map(|(i, p)| html! {
                                    <li key={format!("sol-{}-{}", i, p.solution_latex())} class="solution">
                                        <span class="latex">{format!("\\({}\\)", p.solution_latex())}</span>
                                    </li>
                                })}
                            </ol>
                        </div>
                    </div>
                }
            } else {
                html! {}
            }}

            <footer>
                <p>{"Built with Rust + WebAssembly"}</p>
            </footer>
        </div>
    }
}

fn main() {
    console_error_panic_hook::set_once();
    yew::Renderer::<App>::new().render();
}
