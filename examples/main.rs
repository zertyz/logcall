use logcall::logcall;
use async_trait::async_trait;


// sync demo
////////////


#[logcall(output="info", input="info", skip=[a,b,c])]
fn foo(a: usize) -> usize {
    a + 1
}

#[logcall(ok = "info")]
fn foz(a: usize) -> Result<usize, ()> {
    Ok(a + 1)
}

#[logcall(err = "error")]
fn bar(a: usize) -> Result<usize, String> {
    Err(format!("{}", a + 1))
}

#[logcall(ok = "info", err = "error")]
fn baz(a: usize) -> Result<usize, String> {
    Ok(a + 1)
}


// async demo
/////////////

#[logcall("info")]
async fn async_foo(a: usize) -> usize {
    a + 1
}

#[logcall(err = "error")]
async fn async_bar(a: usize) -> Result<usize, String> {
    Err(format!("{}", a + 1))
}

#[logcall(err = "error", ok = "info")]
async fn async_baz(a: usize) -> Result<usize, String> {
    Ok(a + 1)
}


// native async traits
//////////////////////

trait NativeAsyncTrait {

    #[logcall("info")]
    async fn async_foo(&self, a: usize) -> usize {
        a + 1
    }
    
    async fn async_bar(&self, a: usize) -> Result<usize, String>;
    
    async fn async_baz(&self, a: usize) -> Result<usize, String>;
    
}
struct NativeAsync;
impl NativeAsyncTrait for NativeAsync {

    #[logcall(err = "error")]
    async fn async_bar(&self, a: usize) -> Result<usize, String> {
        Err(format!("{}", a + 1))
    }

    #[logcall(ok = "info", err = "error")]
    async fn async_baz(&self, a: usize) -> Result<usize, String> {
        Ok(a + 1)
    }
}


// legacy async_trait trait
///////////////////////////

#[async_trait]
trait LegacyAsyncTrait {

    #[logcall("info")]
    async fn async_foo(&self, a: usize) -> usize {
        a - 1
    }
    
    #[logcall(err = "error")]
    async fn async_bar(&self, a: usize) -> Result<usize, String> {
        Err(format!("{}", a + 1))
    }
    
    async fn async_baz(&self, a: usize) -> Result<usize, String>;
    
}
struct LegacyAsync;
#[async_trait]
impl LegacyAsyncTrait for LegacyAsync {

    #[logcall("info")]
    async fn async_foo(&self, a: usize) -> usize {
        a + 1
    }

    #[logcall(ok = "info", err = "error")]
    async fn async_baz(&self, a: usize) -> Result<usize, String> {
        Ok(a + 1)
    }
}




#[tokio::main]
async fn main() {

    env_logger::builder()
        .filter_level(log::LevelFilter::Info)
        .init();

    println!("####  SYNC DEMO  ####");

    foo(1);
    foz(1).ok();
    bar(1).ok();
    baz(1).ok();

    println!("####  ASYNC DEMO  ####");

    async_foo(2).await;
    async_bar(2).await.ok();
    async_baz(2).await.ok();

    println!("####  NATIVE ASYNC TRAITS  ####");

    let native_async = NativeAsync;
    native_async.async_foo(3).await;
    native_async.async_bar(3).await.ok();
    native_async.async_baz(3).await.ok();

    println!("####  LEGACY ASYNC TRAITS  ####");

    let legacy_async = LegacyAsync;
    legacy_async.async_foo(4).await;
    legacy_async.async_bar(4).await.ok();
    legacy_async.async_baz(4).await.ok();

}
